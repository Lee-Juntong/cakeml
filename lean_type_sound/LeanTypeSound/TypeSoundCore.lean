/-
  Translation of typeSoundScript.sml (part 1)
  Supporting lemmas for type soundness, up to pattern matching soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.FpSem
import LeanTypeSound.Evaluate
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.EvaluateProps
import LeanTypeSound.Weakening
import LeanTypeSound.TypeSysProps
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.SemanticsMin

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition store_type_extension_def:
  store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))
End
-/
def store_type_extension (tenvS1 tenvS2 : tenv_store) : Prop :=
  ∃ tenvS',
    tenvS2 = Finmap.FUNION tenvS' tenvS1 ∧
    (∀ l, Finmap.FLOOKUP tenvS' l = none ∨ Finmap.FLOOKUP tenvS1 l = none)

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4:
Theorem fst_triple[local]:
  (\ (x,y,z). x) = FST
-/
theorem fst_triple {α β γ : Type} :
    (fun ((x, _, _) : α × β × γ) => x) = (fun (p : α × β × γ) => p.1) := by
  funext p; rfl
/- HOL4:
Theorem sing_list[local]:
  !l. LENGTH l = 1 ⇔ ?x. l = [x]
-/
theorem sing_list {α : Type} :
    ∀ (l : List α), l.length = 1 ↔ ∃ (x : α), l = [x] := by
  intro l
  constructor
  · intro h
    match l, h with
    | [x], _ => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; rfl
/- HOL4:
Theorem EVERY_LIST_REL[local]:
  EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y)
-/
theorem EVERY_LIST_REL_local {α β : Type} :
    ∀ (f : α → β → Prop) (y : β) (l : List α),
      (∀ (x : α), x ∈ l → f x y) ↔ LIST_REL (fun x y => f x y) l (REPLICATE l.length y) := by
  intro f y l
  induction l with
  | nil => exact ⟨fun _ => .nil, fun _ x hx => by simp at hx⟩
  | cons a l ih =>
    simp only [REPLICATE, List.length_cons, List.replicate_succ] at ih ⊢
    constructor
    · intro h
      exact .cons _ _ _ _ (h a List.mem_cons_self) (ih.1 (fun x hx => h x (List.mem_cons_of_mem _ hx)))
    · intro h
      cases h with
      | cons _ _ _ _ h1 h2 =>
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · exact ih.2 h2 x hx
/- HOL4:
Theorem v_unchanged[simp]:
  !tenv x. tenv with v := tenv.v = tenv
-/
theorem v_unchanged :
    ∀ (tenv : type_env), { tenv with v := tenv.v } = tenv := by
  intro tenv; rfl
/- HOL4:
Theorem check_dup_ctors_thm:
  check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
-/
theorem check_dup_ctors_thm :
    ∀ (tvs : List tvarN) (tn : typeN) (condefs : List (conN × List ast_t)),
      check_dup_ctors (tvs, tn, condefs) = ALL_DISTINCT (condefs.map Prod.fst) := by
  intro tvs tn condefs; rfl
theorem ctMap_ok_prim_lookup {ctMap_ : ctMap} {stmp : stamp} {tvs' : List tvarN} {ts : List sem_t}
    {ti : type_ident} (hok : ctMap_ok ctMap_) (hl : Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, ti))
    (hp : ti ∈ prim_type_nums) : ti = Texn_num := by
  cases stmp with
  | TypeStamp cn n => exact absurd (by simpa using hp) (hok.2.2.1 cn n tvs' ts ti hl)
  | ExnStamp n => exact (hok.2.1 n tvs' ts ti hl).2

macro "tv_unfold" : tactic => `(tactic| (simp only [Tint, Tchar, Tstring, Tword8, Tword64, Tdouble,
  Ttup, Tfn, Tref, Tword8array, Tarray, Tvector, Tbool, Texn, Tlist, Tint_num, Tchar_num,
  Tstring_num, Tword8_num, Tword64_num, Tdouble_num, Ttup_num, Tfn_num, Tref_num,
  Tword8array_num, Tarray_num, Tvector_num, Tbool_num, Texn_num, Tlist_num, sem_t.Tapp.injEq,
  List.cons.injEq, reduceCtorEq] at *) <;> (try simp only [Nat.reduceEqDiff, and_false, false_and, false_implies] at *))

theorem type_s_lookup {ctMap_ : ctMap} {envS : List (store_v v)} {tenvS : tenv_store} {n : Nat}
    {st : store_t} (hs : type_s ctMap_ envS tenvS) (hl : Finmap.FLOOKUP tenvS n = some st) :
    ∃ sv, store_lookup n envS = some sv ∧ type_sv ctMap_ tenvS sv st := by
  obtain ⟨sv, hsv⟩ := ((hs n).1).1 ⟨st, hl⟩
  exact ⟨sv, hsv, (hs n).2 st sv ⟨hl, hsv⟩⟩

set_option hygiene false in
macro "tv_close" : tactic => `(tactic| first
    | exact ⟨_, rfl⟩
    | (obtain ⟨_, rfl⟩ := hT; exact absurd (ctMap_ok_prim_lookup (by first | exact hok | exact hok.1) (by assumption) (by decide)) (by decide))
    | (obtain ⟨t1', t2', rfl, -⟩ := type_funs_Tfn _ _ _ _ 0 _ _ ⟨by assumption, by assumption⟩; tv_unfold)
    | skip)

/- HOL4:
Theorem prim_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap ⇒ (∃s. v = Litv (StrLit s))) ∧
  (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word64 n))) ∧
  (type_v tvs ctMap tenvS v Tdouble ∧ ctMap_ok ctMap ⇒ ∃n. v = Litv (Float64 n)) ∧
  (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap ⇒
   (∃vs. v = Conv NONE vs ∧ LENGTH ts = LENGTH vs)) ∧
  (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap ⇒
   (∃env n e. v = Closure env n e) ∨
   (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n v2. v = Loc T n ∧ store_lookup n envS = SOME (Refv v2) ∧
           type_v 0 ctMap tenvS v2 t1)) ∧
  (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n ws. v = Loc T n ∧ store_lookup n envS = SOME (W8array ws) ∧
           FLOOKUP tenvS n = SOME W8array_t)) ∧
  (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n vs. v = Loc T n ∧ store_lookup n envS = SOME (Varray vs) ∧
           EVERY (\v. type_v 0 ctMap tenvS v t) vs ∧
           FLOOKUP tenvS n = SOME (Varray_t t))) ∧
  (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap ⇒
   (?vs. v = Vectorv vs ∧ EVERY (\v. type_v tvs ctMap tenvS v t) vs))
-/
theorem prim_canonical_values_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v)
      (envS : List (store_v v)) (ts : List sem_t) (t1 t2 t : sem_t),
    (type_v tvs ctMap_ tenvS val_ Tint ∧ ctMap_ok ctMap_ →
      ∃ (n : Int), val_ = .Litv (.IntLit n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tchar ∧ ctMap_ok ctMap_ →
      ∃ (c : Char), val_ = .Litv (.Char c)) ∧
    (type_v tvs ctMap_ tenvS val_ Tstring ∧ ctMap_ok ctMap_ →
      ∃ (s : mlstring), val_ = .Litv (.StrLit s)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8 ∧ ctMap_ok ctMap_ →
      ∃ (n : word8), val_ = .Litv (.Word8 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword64 ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Word64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tdouble ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Float64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Ttup ts) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v), val_ = .Conv none vs ∧ ts.length = vs.length) ∧
    (type_v tvs ctMap_ tenvS val_ (Tfn t1 t2) ∧ ctMap_ok ctMap_ →
      (∃ (env : sem_env) (n : varN) (e : exp), val_ = .Closure env n e) ∨
      (∃ (env : sem_env) (funs : List (varN × varN × exp)) (n : varN),
        val_ = .Recclosure env funs n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tref t1) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (v2 : v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Refv v2) ∧
        type_v 0 ctMap_ tenvS v2 t1) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8array ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (ws : List word8),
        val_ = .Loc true n ∧ store_lookup n envS = some (.W8array ws) ∧
        Finmap.FLOOKUP tenvS n = some .W8array_t) ∧
    (type_v tvs ctMap_ tenvS val_ (Tarray t) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (vs : List v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Varray vs) ∧
        (∀ (v_ : v), v_ ∈ vs → type_v 0 ctMap_ tenvS v_ t) ∧
        Finmap.FLOOKUP tenvS n = some (.Varray_t t)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tvector t) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v),
        val_ = .Vectorv vs ∧ (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t)) := by
  intro tvs ctMap_ tenvS val_ envS ts t1 t2 t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, hok⟩
    generalize hT : Tint = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Tchar = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Tstring = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Tword8 = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Tword64 = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Tdouble = T at h
    cases h <;> (try tv_unfold) <;> tv_close
  · rintro ⟨h, hok⟩
    generalize hT : Ttup ts = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    obtain ⟨rfl, -⟩ := hT; exact ⟨_, rfl, by omega⟩
  · rintro ⟨h, hok⟩
    generalize hT : Tfn t1 t2 = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    · exact Or.inl ⟨_, _, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩
  · rintro ⟨h, hok, hs⟩
    generalize hT : Tref t1 = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    rename_i t' n _ hl
    obtain ⟨⟨rfl, -⟩, -⟩ := hT
    obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨_, _, rfl, h1, h2⟩
  · rintro ⟨h, hok, hs⟩
    generalize hT : Tword8array = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    rename_i n hl
    obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨_, _, rfl, h1, hl⟩
  · rintro ⟨h, hok, hs⟩
    generalize hT : Tarray t = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    rename_i t' n _ hl
    obtain ⟨⟨rfl, -⟩, -⟩ := hT
    obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨_, _, rfl, h1, h2, hl⟩
  · rintro ⟨h, hok⟩
    generalize hT : Tvector t = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    rename_i t' vs _ hall
    obtain ⟨⟨rfl, -⟩, -⟩ := hT
    exact ⟨_, rfl, hall⟩
theorem ctMap_list_stamp {ctMap_ : ctMap} {stmp : stamp} {tvs' : List tvarN} {ts : List sem_t}
    (hok : ctMap_ok ctMap_) (hb : ctMap_has_lists ctMap_)
    (hl : Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, Tlist_num)) :
    (stmp = .TypeStamp (mlstring.strlit "[]") list_type_num ∧ tvs' = [mlstring.strlit "'a"] ∧ ts = []) ∨
    (stmp = .TypeStamp (mlstring.strlit "::") list_type_num ∧ tvs' = [mlstring.strlit "'a"] ∧
      ts = [.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))]) := by
  have hs := hok.2.2.2 stmp _ _ _ _ _ _ ⟨hl, hb.1⟩
  cases stmp with
  | ExnStamp n => simp [same_type] at hs
  | TypeStamp cn n =>
    simp only [same_type, beq_iff_eq] at hs
    subst hs
    by_cases h1 : cn = mlstring.strlit "[]"
    · subst h1; rw [hb.1] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl
      exact Or.inl ⟨rfl, hl.1.symm, hl.2.1.symm⟩
    · by_cases h2 : cn = mlstring.strlit "::"
      · subst h2; rw [hb.2.1] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl
        exact Or.inr ⟨rfl, hl.1.symm, hl.2.1.symm⟩
      · rw [hb.2.2 cn ⟨h2, h1⟩] at hl; cases hl

/- HOL4:
Theorem has_lists_v_to_list[local]:
  !ctMap tvs tenvS t3.
    ctMap_ok ctMap ∧
    ctMap_has_lists ctMap ∧
    type_v tvs ctMap tenvS v (Tlist t3)
    ⇒
    ?vs. v_to_list v = SOME vs ∧
         EVERY (\v. type_v tvs ctMap tenvS v t3) vs ∧
         (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
         (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str)
-/
theorem has_lists_v_to_list :
    ∀ (ctMap_ : ctMap) (tvs : Nat) (tenvS : tenv_store) (t3 : sem_t) (val_ : v),
      ctMap_ok ctMap_ ∧
      ctMap_has_lists ctMap_ ∧
      type_v tvs ctMap_ tenvS val_ (Tlist t3) →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t3) ∧
        (t3 = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t3 = Tstring → ∃ (str : mlstring), vs_to_string vs = some str) := by
  intro ctMap_ tvs tenvS t3 val_ ⟨hok, hlists, h⟩
  generalize hT : Tlist t3 = T at h
  induction h generalizing t3 with
  | conv_some tvs ctMap_ tenvS ts' tvs' vs ts ti stmp hfv hlen hvl hall hl ih =>
    simp only [Tlist, sem_t.Tapp.injEq] at hT
    obtain ⟨rfl, rfl⟩ := hT
    rcases ctMap_list_stamp hok hlists hl with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hvl)
      subst this
      refine ⟨[], by simp [v_to_list], by simp, fun _ => ⟨[], by simp [v_to_char_list]⟩,
        fun _ => ⟨_, rfl⟩⟩
    · match vs, hvl, hall, ih with
      | [v1, v2], _, hall, ih =>
        have h1 := hall 0 (by simp)
        have hsub : ∀ t, type_subst (Finmap.FUPDATE_LIST Finmap.FEMPTY
            ([mlstring.strlit "'a"].zip [t]).reverse) (.Tvar (mlstring.strlit "'a")) = t := by
          intro t; simp [type_subst, Finmap.FUPDATE_LIST, Finmap.FUPDATE, Finmap.FLOOKUP]
        simp only [List.map, hsub] at h1
        have ih2 := ih 1 (by simp) t3 hok hlists (by simp [Tlist, type_subst, Finmap.FUPDATE_LIST, Finmap.FUPDATE, Finmap.FLOOKUP])
        obtain ⟨vs2, hv2, hall2, hc2, hs2⟩ := ih2
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hv2 hc2
        refine ⟨v1 :: vs2, by simp [v_to_list, hv2], ?_, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact h1
          · exact hall2 w hw
        · intro hc; subst hc
          obtain ⟨c, rfl⟩ := (prim_canonical_values_thm _ _ _ _ [] [] (.Tvar_db 0) (.Tvar_db 0) (.Tvar_db 0)).2.1 ⟨h1, hok⟩
          obtain ⟨cs, hcs⟩ := hc2 rfl
          exact ⟨c :: cs, by simp [v_to_char_list, hcs]⟩
        · intro hs; subst hs
          obtain ⟨s, rfl⟩ := (prim_canonical_values_thm _ _ _ _ [] [] (.Tvar_db 0) (.Tvar_db 0) (.Tvar_db 0)).2.2.1 ⟨h1, hok⟩
          obtain ⟨str, hstr⟩ := hs2 rfl
          exact ⟨strcat s str, by simp [vs_to_string, hstr]⟩
  | recclosure =>
    rename_i hf hl _ _ _
    obtain ⟨t1', t2', rfl, -⟩ := type_funs_Tfn _ _ _ _ 0 _ _ ⟨hf, hl⟩
    simp [Tlist, Tfn, Tlist_num, Tfn_num] at hT
  | _ => tv_unfold
theorem ctMap_bool_stamp {ctMap_ : ctMap} {stmp : stamp} {tvs' : List tvarN} {ts : List sem_t}
    (hok : ctMap_ok ctMap_) (hb : ctMap_has_bools ctMap_)
    (hl : Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, Tbool_num)) :
    (stmp = .TypeStamp (mlstring.strlit "True") bool_type_num ∨
     stmp = .TypeStamp (mlstring.strlit "False") bool_type_num) ∧ tvs' = [] ∧ ts = [] := by
  have hs := hok.2.2.2 stmp _ _ _ _ _ _ ⟨hl, hb.1⟩
  cases stmp with
  | ExnStamp n => simp [same_type] at hs
  | TypeStamp cn n =>
    simp only [same_type, beq_iff_eq] at hs
    subst hs
    by_cases h1 : cn = mlstring.strlit "True"
    · subst h1; rw [hb.1] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl
      exact ⟨Or.inl rfl, hl.1.symm, hl.2.1.symm⟩
    · by_cases h2 : cn = mlstring.strlit "False"
      · subst h2; rw [hb.2.1] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl
        exact ⟨Or.inr rfl, hl.1.symm, hl.2.1.symm⟩
      · rw [hb.2.2 cn ⟨h1, h2⟩] at hl; cases hl

/- HOL4:
Theorem ctor_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
   (∃b. v = Boolv b)) ∧
  (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap ⇒
   ?vs.
     v_to_list v = SOME vs ∧
     EVERY (\v. type_v tvs ctMap tenvS v t) vs ∧
     (t = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
     (t = Tstring ⇒ ∃str. vs_to_string vs = SOME str)) ∧
  (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
   ctMap_ok ctMap ∧
   FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ⇒
   (?cn n vs. same_type stamp (TypeStamp cn n) ∧ v = Conv (SOME (TypeStamp cn n)) vs) ∨
   (?n vs. same_type stamp (ExnStamp n) ∧ v = Conv (SOME (ExnStamp n)) vs))
-/
theorem ctor_canonical_values_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v)
      (t : sem_t) (ts : List sem_t) (ti : type_ident)
      (stmp : stamp) (tvs' : List tvarN) (ts' : List sem_t),
    (type_v tvs ctMap_ tenvS val_ Tbool ∧ ctMap_ok ctMap_ ∧ ctMap_has_bools ctMap_ →
      ∃ (b : Bool), val_ = Boolv b) ∧
    (type_v tvs ctMap_ tenvS val_ (Tlist t) ∧ ctMap_ok ctMap_ ∧ ctMap_has_lists ctMap_ →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t) ∧
        (t = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t = Tstring → ∃ (str : mlstring), vs_to_string vs = some str)) ∧
    (type_v tvs ctMap_ tenvS val_ (.Tapp ts ti) ∧
     ctMap_ok ctMap_ ∧
     Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts', ti) →
      (∃ (cn : conN) (n : Nat) (vs : List v),
        same_type stmp (.TypeStamp cn n) ∧ val_ = .Conv (some (.TypeStamp cn n)) vs) ∨
      (∃ (n : Nat) (vs : List v),
        same_type stmp (.ExnStamp n) ∧ val_ = .Conv (some (.ExnStamp n)) vs)) := by
  intro tvs ctMap_ tenvS val_ t ts ti stmp tvs' ts'
  refine ⟨?_, fun ⟨h, hok, hl⟩ => has_lists_v_to_list _ _ _ _ _ ⟨hok, hl, h⟩, ?_⟩
  · rintro ⟨h, hok, hb⟩
    generalize hT : Tbool = T at h
    cases h <;> (try tv_unfold) <;> tv_close
    rename_i hvl _ hl _
    obtain ⟨rfl, rfl⟩ := hT
    obtain ⟨hst, rfl, rfl⟩ := ctMap_bool_stamp hok hb hl
    have : _ = [] := List.eq_nil_of_length_eq_zero (by simpa using hvl)
    subst this
    rcases hst with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  rintro ⟨h, hok, hl⟩
  generalize hT : sem_t.Tapp ts ti = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  · rename_i stmp0 _ _ _ hl0 _
    obtain ⟨rfl, rfl⟩ := hT
    have hs := hok.2.2.2 stmp _ _ _ stmp0 _ _ ⟨hl, hl0⟩
    cases stmp0 with
    | TypeStamp cn n => exact Or.inl ⟨cn, n, _, hs, rfl⟩
    | ExnStamp n => exact Or.inr ⟨n, _, hs, rfl⟩
  · obtain ⟨_, rfl⟩ := hT
    exact absurd (ctMap_ok_prim_lookup hok hl (by decide)) (by decide)
/- HOL4:
Theorem same_type_refl[local]:
  !t. same_type t t
-/
theorem same_type_refl :
    ∀ (t : stamp), same_type t t := by
  intro t; cases t <;> simp [same_type]
theorem do_eq_list_ne_of_zip : ∀ (vs1 vs2 : List v),
    (∀ a b, (a, b) ∈ vs1.zip vs2 → do_eq a b ≠ .Eq_type_error) →
    do_eq_list vs1 vs2 ≠ .Eq_type_error
  | [], [], _ => by simp [do_eq_list]
  | [], _ :: _, _ => by simp [do_eq_list]
  | _ :: _, [], _ => by simp [do_eq_list]
  | a :: as, b :: bs, h => by
    have h1 := h a b (by simp)
    have ih := do_eq_list_ne_of_zip as bs (fun x y hm => h x y (by simp [hm]))
    simp only [do_eq_list]
    split
    · split <;> simp_all
    · simp_all

theorem mem_zip_getElem_bang {α β : Type} [Inhabited α] [Inhabited β] {l1 : List α} {l2 : List β}
    {a : α} {b : β} (h : (a, b) ∈ l1.zip l2) :
    ∃ i, i < l1.length ∧ i < l2.length ∧ l1[i]! = a ∧ l2[i]! = b := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_zip, Nat.lt_min] at hi
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  refine ⟨i, hi.1, hi.2, ?_, ?_⟩
  · rw [getElem!_pos l1 i hi.1]; exact he.1
  · rw [getElem!_pos l2 i hi.2]; exact he.2

theorem eq_same_type_v (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (hok : ctMap_ok ctMap_) :
    ∀ (n : Nat) (v1 v2 : v) (t : sem_t), sizeOf v1 < n → type_v tvs ctMap_ tenvS v1 t → type_v tvs ctMap_ tenvS v2 t →
      do_eq v1 v2 ≠ .Eq_type_error := by
  intro n
  induction n with
  | zero => intro _ _ _ h; omega
  | succ n ih =>
  intro v1 v2 t hs h1 h2
  generalize hT : t = T at h2
  cases h1 <;> cases h2 <;> (try tv_unfold) <;> tv_close
  all_goals (try simp [do_eq, lit_same_type])
  · rename_i ts1 tvs1 vs1 tss1 ti1 st1 _ hl1 _ hl1' hv1 ts2 tvs2 vs2 tss2 ti2 st2 _ hl2 _ hl2' hv2
    obtain ⟨rfl, rfl⟩ := hT
    by_cases hst : st1 = st2
    · subst hst
      rw [hl1'] at hl2'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl2'
      obtain ⟨rfl, rfl, -⟩ := hl2'
      split
      · apply do_eq_list_ne_of_zip
        intro a b hab
        have hm := List.sizeOf_lt_of_mem (List.of_mem_zip hab).1
        obtain ⟨i, hi1, hi2, rfl, rfl⟩ := mem_zip_getElem_bang hab
        refine ih _ _ _ ?_ (hv1 i hi1) (hv2 i hi2)
        simp at hs; omega
      · simp [ctor_same_type, same_type_refl]
    · have := hok.2.2.2 _ _ _ _ _ _ _ ⟨hl1', hl2'⟩
      split
      · simp_all
      · simp [ctor_same_type, this]
  · obtain ⟨rfl, rfl⟩ := hT
    exact absurd (ctMap_ok_prim_lookup hok ‹_› (by decide)) (by decide)
  · rename_i vs1 ts1 hl1 hv1 vs2 ts2 hl2 hv2
    obtain ⟨rfl, -⟩ := hT
    split
    · apply do_eq_list_ne_of_zip
      intro a b hab
      have hm := List.sizeOf_lt_of_mem (List.of_mem_zip hab).1
      obtain ⟨i, hi1, hi2, rfl, rfl⟩ := mem_zip_getElem_bang hab
      refine ih _ _ _ ?_ (hv1 i hi1) (hv2 i (by omega))
      simp at hs; omega
    · simp [ctor_same_type]
  · obtain ⟨rfl, rfl⟩ := hT
    exact absurd (ctMap_ok_prim_lookup hok ‹_› (by decide)) (by decide)
  · rename_i t1 vs1 _ hv1 t2 vs2 _ hv2
    obtain ⟨⟨rfl, -⟩, -⟩ := hT
    split
    · apply do_eq_list_ne_of_zip
      intro a b hab
      have hm := List.sizeOf_lt_of_mem (List.of_mem_zip hab).1
      refine ih _ _ _ ?_ (hv1 _ (List.of_mem_zip hab).1) (hv2 _ (List.of_mem_zip hab).2)
      simp at hs; omega
    · simp

/- HOL4:
Theorem eq_same_type[local]:
  (!v1 v2 tvs ctMap cns tenvS t.
     ctMap_ok ctMap ∧
     type_v tvs ctMap tenvS v1 t ∧
     type_v tvs ctMap tenvS v2 t
     ⇒
     do_eq v1 v2 ≠ Eq_type_error) ∧
  (!vs1 vs2 tvs ctMap cns tenvS ts.
     ctMap_ok ctMap ∧
     LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
     LIST_REL (type_v tvs ctMap tenvS) vs2 ts
     ⇒
     do_eq_list vs1 vs2 ≠ Eq_type_error)
-/
theorem eq_same_type :
    (∀ (v1 v2 : v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_v tvs ctMap_ tenvS v1 t ∧
      type_v tvs ctMap_ tenvS v2 t →
      do_eq v1 v2 ≠ .Eq_type_error) ∧
    (∀ (vs1 vs2 : List v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (ts : List sem_t),
      ctMap_ok ctMap_ ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs1 ts ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs2 ts →
      do_eq_list vs1 vs2 ≠ .Eq_type_error) := by
  refine ⟨fun v1 v2 tvs ctMap_ _ tenvS t ⟨hok, h1, h2⟩ =>
    eq_same_type_v tvs ctMap_ tenvS hok _ v1 v2 t (Nat.lt_succ_self _) h1 h2, ?_⟩
  intro vs1 vs2 tvs ctMap_ _ tenvS ts ⟨hok, h1, h2⟩
  induction h1 generalizing vs2 with
  | nil => cases h2; simp [do_eq_list]
  | cons a t as ts ha _ ih =>
    cases h2 with
    | cons b _ bs _ hb hbs =>
      have e1 := eq_same_type_v tvs ctMap_ tenvS hok _ a b t (Nat.lt_succ_self _) ha hb
      have e2 := ih bs hbs
      simp only [do_eq_list]
      split
      · split <;> simp_all
      · simp_all
/- HOL4:
Theorem type_env_conv_thm[local]:
  ∀ctMap envC tenvC.
    nsAll2 (type_ctor ctMap) envC tenvC ⇒
    ∀cn tvs ts tn ti.
      (nsLookup tenvC cn = SOME (tvs,ts,ti) ⇒
       ?cn' stamp.
         nsLookup envC cn = SOME (LENGTH ts,stamp) ∧
         FLOOKUP ctMap stamp = SOME (tvs, ts, ti)) ∧
      (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)
-/
theorem type_env_conv_thm :
    ∀ (ctMap_ : ctMap) (envC : env_ctor) (tenvC : tenv_ctor),
      nsAll2 (type_ctor ctMap_) envC tenvC →
      ∀ (cn : cml_id modN conN) (tvs' : List tvarN) (ts : List sem_t) (tn : type_ident) (ti : type_ident),
        (nsLookup tenvC cn = some (tvs', ts, tn) →
          ∃ (cn' : conN) (stmp : stamp),
            nsLookup envC cn = some (ts.length, stmp) ∧
            Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, tn)) ∧
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := by
  intro ctMap_ envC tenvC h cn tvs' ts tn _
  refine ⟨fun hl => ?_, fun hl => (nsAll2_nsLookup_none _ _ _ cn h).2 hl⟩
  obtain ⟨⟨k, st⟩, h1, h2, h3⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, h⟩
  refine ⟨default, st, ?_, h2⟩
  simp only at h3; rw [h1, h3]
/- HOL4:
Theorem type_funs_fst[local]:
  !tenv tenvE funs tenv'.
    type_funs tenv tenvE funs tenv'
    ⇒
    MAP FST funs = MAP FST tenv'
-/
theorem type_funs_fst :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (tenv' : List (varN × sem_t)),
      type_funs tenv tenvE funs tenv' →
      funs.map Prod.fst = tenv'.map Prod.fst := by
  intro tenv tenvE funs
  induction funs generalizing tenvE with
  | nil => intro tenv' h; cases h; rfl
  | cons f funs ih =>
    intro tenv' h
    cases h with
    | cons _ fn n e t1 t2 _ bindings h1 h2 h3 h4 =>
      simp [ih _ _ h3]
theorem type_v_recclosure_of_env {ctMap_ : ctMap} {tenvS : tenv_store} {tenv : type_env}
    {tenvE : tenv_val_exp} {env : sem_env} {tvs : Nat} {funs : List (varN × varN × exp)}
    {bindings : List (varN × sem_t)} {fn_ : varN} {t : sem_t}
    (htok : tenv_ok tenv) (hEok : tenv_val_exp_ok tenvE) (h0 : num_tvs tenvE = 0)
    (henv : type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v })
    (hf : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings)
    (hl : ALOOKUP bindings fn_ = some t) (hd : ALL_DISTINCT (funs.map Prod.fst)) :
    type_v tvs ctMap_ tenvS (.Recclosure env funs fn_) t := by
  obtain ⟨hc, hv⟩ := henv
  have hv' := hv
  obtain ⟨⟨s1, m1⟩, ⟨_, m2⟩⟩ := hv'
  refine .recclosure _ _ _ tenv tenvE env fn_ funs bindings t htok hEok h0 hc
    (fun id_ => nsAll2_nsLookup_none _ _ _ id_ hv) m1 m2 ?_ hf hl hd ?_
  · intro id_ val_ p h1 h2
    obtain ⟨p', h1', h2'⟩ := s1 id_ val_ h1
    simp only at h1'
    rw [h1'] at h2; cases h2; exact h2'
  · rw [type_funs_fst _ _ _ _ hf]
    exact List.mem_map.2 ⟨_, ALOOKUP_mem hl, rfl⟩

/- HOL4:
Theorem type_recfun_env_help[local]:
  ∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
    ALL_DISTINCT (MAP FST funs') ∧
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
-/
theorem type_recfun_env_help :
    ∀ (fn_ : varN) (funs funs' : List (varN × varN × exp)) (ctMap_ : ctMap)
      (tenv : type_env) (bindings : List (varN × sem_t)) (tenvE : tenv_val_exp)
      (env : sem_env) (tenvS : tenv_store) (tvs : Nat) (bindings' : List (varN × sem_t)),
      ALL_DISTINCT (funs'.map Prod.fst) ∧
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      (∀ (fn_ : varN) (t : sem_t), ALOOKUP bindings fn_ = some t → ALOOKUP bindings' fn_ = some t) ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs' p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := by
  intro _ funs funs' ctMap_ tenv bindings tenvE env tenvS tvs bindings'
    ⟨hd, htok, henv, hEok, h0, hsub, hf', hf⟩
  induction funs generalizing bindings with
  | nil => cases hf; exact .nil
  | cons f funs ih =>
    cases hf with
    | cons _ fn n e t1 t2 _ bs _ _ hrest hnone =>
      refine .cons _ _ _ _ ⟨rfl, ?_⟩ (ih bs (fun fn' t' hl => hsub fn' t' ?_) hrest)
      · exact type_v_recclosure_of_env htok hEok h0 henv hf'
          (hsub fn _ (by simp [ALOOKUP])) hd
      · simp only [ALOOKUP]
        split
        · rename_i he; simp at he; subst he; rw [hnone] at hl; cases hl
        · exact hl
/- HOL4:
Theorem type_recfun_env[local]:
  ∀funs ctMap tenvS tvs tenv tenvE env bindings.
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
-/
theorem type_recfun_env :
    ∀ (funs : List (varN × varN × exp)) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tvs : Nat) (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env)
      (bindings : List (varN × sem_t)),
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALL_DISTINCT (funs.map Prod.fst) →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := by
  intro funs ctMap_ tenvS tvs tenv tenvE env bindings ⟨htok, henv, hEok, h0, hf, hd⟩
  exact type_recfun_env_help default funs funs ctMap_ tenv bindings tenvE env tenvS tvs bindings
    ⟨hd, htok, henv, hEok, h0, fun _ _ h => h, hf, hf⟩
/- HOL4:
val type_v_exn = Q.prove (
  `!tvs cenv senv.
     ctMap_has_exns cenv ⇒
   type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn ∧
   type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`)
-/
theorem type_v_exn :
    ∀ (tvs : Nat) (cenv : ctMap) (senv : tenv_store),
      ctMap_has_exns cenv →
      type_v tvs cenv senv (.Conv (some chr_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some subscript_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some bind_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some div_stamp) []) Texn := by
  intro tvs cenv senv ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact .conv_some _ _ _ [] [] [] [] Texn_num _ (fun _ h => by cases h) rfl rfl
      (fun i hi => by simp at hi) (by assumption)
/- HOL4:
Theorem type_v_Boolv[local]:
  ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool
-/
theorem type_v_Boolv :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (b : Bool),
      ctMap_has_bools ctMap_ → type_v tvs ctMap_ tenvS (Boolv b) Tbool := by
  intro tvs ctMap_ tenvS b ⟨h1, h2, _⟩
  cases b
  · exact .conv_some _ _ _ [] [] [] [] Tbool_num _ (fun _ h => by cases h) rfl rfl
      (fun i hi => by simp at hi) h2
  · exact .conv_some _ _ _ [] [] [] [] Tbool_num _ (fun _ h => by cases h) rfl rfl
      (fun i hi => by simp at hi) h1
/- HOL4:
Theorem remove_lambda_prod[local]:
  (\ (x,y). P x y) = (\xy. P (FST xy) (SND xy))
-/
theorem remove_lambda_prod {α β γ : Type} :
    ∀ (P : α → β → γ),
      (fun ((x, y) : α × β) => P x y) = (fun (p : α × β) => P p.1 p.2) := by
  intro P; funext p; rfl
theorem nsAll2_of_closure_conds {ctMap_ : ctMap} {tenvS : tenv_store}
    {ev : «namespace» modN varN v} {tv : tenv_val}
    (h1 : ∀ (id_ : cml_id modN varN), (nsLookup ev id_ = none ↔ nsLookup tv id_ = none))
    (h2 : ∀ (path : List modN), nsLookupMod tv path = none → nsLookupMod ev path = none)
    (h3 : ∀ (path : List modN), nsLookupMod ev path = none → nsLookupMod tv path = none)
    (h4 : ∀ (id_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t),
      nsLookup ev id_ = some val_ → nsLookup tv id_ = some p → type_v p.1 ctMap_ tenvS val_ p.2) :
    nsAll2 (fun _ v_ p => type_v p.1 ctMap_ tenvS v_ p.2) ev tv := by
  refine ⟨⟨fun id_ val_ hl => ?_, h2⟩, ⟨fun id_ p hl => ?_, h3⟩⟩
  · cases hp : nsLookup tv id_ with
    | none => rw [← h1] at hp; rw [hp] at hl; cases hl
    | some p => exact ⟨p, rfl, h4 id_ val_ p hl hp⟩
  · cases hv : nsLookup ev id_ with
    | none => rw [h1] at hv; rw [hv] at hl; cases hl
    | some val_ => exact ⟨val_, rfl, h4 id_ val_ p hv hl⟩

theorem build_rec_env_nsBindList (funs : List (varN × varN × exp)) (env : sem_env)
    (e : «namespace» modN varN v) :
    build_rec_env funs env e =
      nsBindList (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs p.1))) e := by
  unfold build_rec_env nsBindList
  rw [List.foldr_map]

/- HOL4:
Theorem opapp_type_sound:
  !ctMap tenvS vs ts t.
    ctMap_ok ctMap ∧
    type_op Opapp ts t ∧
    LIST_REL (type_v 0 ctMap tenvS) vs ts
    ⇒
    ?env e tenv tenvE.
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
      type_e tenv tenvE e t ∧
      do_opapp vs = SOME (env,e)
-/
theorem opapp_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v) (ts : List sem_t) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_op .Opapp ts t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts →
      ∃ (env : sem_env) (e : exp) (tenv : type_env) (tenvE : tenv_val_exp),
        tenv_ok tenv ∧
        tenv_val_exp_ok tenvE ∧
        num_tvs tenvE = 0 ∧
        type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
        type_e tenv tenvE e t ∧
        do_opapp vs = some (env, e) := by
  intro ctMap_ tenvS vs ts t ⟨hok, hop, hrel⟩
  rcases hrel with _ | ⟨f, tf, _, _, hf, hrel⟩
  · simp [type_op] at hop
  rcases hrel with _ | ⟨a, ta, _, _, ha, hrel⟩
  · simp [type_op] at hop
  rcases hrel with _ | ⟨_, _, _, _, _, _⟩
  rotate_left; · simp [type_op] at hop
  simp only [type_op] at hop
  subst hop
  rcases (prim_canonical_values_thm 0 ctMap_ tenvS f [] [] ta t t).2.2.2.2.2.2.2.1 ⟨hf, hok⟩ with
    ⟨env, n, e, rfl⟩ | ⟨env, funs, n, rfl⟩
  · generalize hT : Tfn ta t = T at hf
    cases hf with
    | closure _ _ _ tenv tenvE _ _ _ t1 t2 htok hEok h0 hc c1 c2 c3 c4 hfv hty =>
      simp only [Tfn, sem_t.Tapp.injEq, List.cons.injEq, and_true] at hT
      obtain ⟨rfl, rfl⟩ := hT
      refine ⟨.mk (nsBind n a env.v_) env.c, e, tenv, .Bind_name n 0 ta tenvE, htok, ?_, by simpa [num_tvs] using h0,
        ⟨hc, ?_⟩, by simpa [bind_tvar0] using hty, rfl⟩
      · simp only [tenv_val_exp_ok, h0, Nat.add_zero]; exact ⟨hfv, hEok⟩
      · simp only [add_tenvE]
        exact nsAll2_nsBind _ _ _ _ _ _ ⟨ha, nsAll2_of_closure_conds c1 c2 c3 c4⟩
  · generalize hT : Tfn ta t = T at hf
    cases hf with
    | recclosure _ _ _ tenv tenvE _ _ _ bindings _ htok hEok h0 hc c1 c2 c3 c4 hfs hl hd hm =>
      subst hT
      have hfs' : type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings := by
        simpa [bind_tvar0] using hfs
      obtain ⟨x, e, hfind⟩ := type_funs_find_recfun n [] funs bindings (.Lit (.IntLit 0)) tenv _ _
        ⟨hl, hfs'⟩
      obtain ⟨hty, hfv⟩ := type_recfun_lookup_aux hfs' n x e ta t hfind hl
      have hEok' : tenv_val_exp_ok (bind_var_list 0 bindings tenvE) :=
        tenv_val_exp_ok_bvl _ _ ⟨hEok, by
          simp only [EVERY, List.all_eq_true, List.mem_map]
          rintro _ ⟨b, hb, rfl⟩
          have := type_funs_freevars_aux hfs' b hb
          rwa [num_tvs_bind_var_list] at this⟩
      have h0' : num_tvs (bind_var_list 0 bindings tenvE) = 0 := by
        rw [num_tvs_bind_var_list]; omega
      refine ⟨.mk (nsBind x a (build_rec_env funs env env.v_)) env.c, e, tenv, .Bind_name x 0 ta (bind_var_list 0 bindings tenvE), htok, ?_,
        by simpa [num_tvs] using h0', ⟨hc, ?_⟩, hty, ?_⟩
      · simp only [tenv_val_exp_ok, h0', Nat.add_zero]
        refine ⟨?_, hEok'⟩
        simp only [Tfn, check_freevars_Tapp] at hfv
        rw [h0'] at hfv
        simp at hfv
        exact hfv.1
      · simp only [add_tenvE]
        refine nsAll2_nsBind (m := modN) (n := varN) (fun _ v_ p => type_v p.1 ctMap_ tenvS v_ p.2) x a (0, ta) _ _ ⟨ha, ?_⟩
        rw [add_tenvE_bvl, build_rec_env_nsBindList]
        refine nsAll2_nsBindList _ _ _ _ _ ⟨?_, nsAll2_of_closure_conds c1 c2 c3 c4⟩
        have := type_recfun_env funs ctMap_ tenvS 0 tenv tenvE env bindings
          ⟨htok, ⟨hc, nsAll2_of_closure_conds c1 c2 c3 c4⟩, hEok, h0, hfs, hd⟩
        simpa using this
      · have hd' : ALL_DISTINCT (funs.map fun (p : varN × varN × exp) => p.1) = true := hd
        simp only [do_opapp, hd', hfind, if_true]
/- HOL4:
Theorem store_type_extension_weakS:
  !tenvS1 tenvS2.
    store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1
-/
theorem store_type_extension_weakS :
    ∀ (tenvS1 tenvS2 : tenv_store),
      store_type_extension tenvS1 tenvS2 → weakS tenvS2 tenvS1 := by
  intro s1 s2 ⟨s', he, hd⟩ k val_ hk
  subst he
  simp only [Finmap.FUNION]
  rcases hd k with h | h
  · simp only [Finmap.FLOOKUP] at h; rw [h]; exact hk
  · simp only [Finmap.FLOOKUP] at h; rw [h] at hk; cases hk
/- HOL4:
Theorem store_type_extension_refl:
  !tenvS. store_type_extension tenvS tenvS
-/
theorem store_type_extension_refl :
    ∀ (tenvS : tenv_store), store_type_extension tenvS tenvS := by
  intro tenvS
  exact ⟨Finmap.FEMPTY, by funext x; rfl, fun l => Or.inl rfl⟩
/- HOL4:
Theorem store_type_extension_trans:
  !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3
-/
theorem store_type_extension_trans :
    ∀ (s1 s2 s3 : tenv_store),
      store_type_extension s1 s2 ∧ store_type_extension s2 s3 →
      store_type_extension s1 s3 := by
  intro s1 s2 s3 ⟨⟨a, ha, hda⟩, ⟨b, hb, hdb⟩⟩
  refine ⟨Finmap.FUNION b a, ?_, ?_⟩
  · subst ha hb; funext x; simp only [Finmap.FUNION]; split <;> rfl
  · intro l
    simp only [Finmap.FLOOKUP] at hda hdb ⊢
    cases h1 : s1 l with
    | none => exact Or.inr rfl
    | some w =>
      left
      have ha' : a l = none := by rcases hda l with h | h; exact h; rw [h] at h1; cases h1
      have hs2 : s2 l = some w := by subst ha; simp [Finmap.FUNION, ha', h1]
      have hb' : b l = none := by rcases hdb l with h | h; exact h; rw [h] at hs2; cases hs2
      simp [Finmap.FUNION, ha', hb']
theorem store_lookup_some_iff {α : Type} {l : Nat} {st : List (store_v α)} :
    (∃ x, store_lookup l st = some x) ↔ l < st.length := by
  unfold store_lookup; split <;> simp_all

/- HOL4:
Theorem store_assign_type_sound:
  !ctMap tenvS store sv st l.
    type_s ctMap store tenvS ∧
    FLOOKUP tenvS l = SOME st ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store'.
      store_assign l sv store = SOME store' ∧
      type_s ctMap store' tenvS
-/
theorem store_assign_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t) (l : Nat),
      type_s ctMap_ store_ tenvS ∧
      Finmap.FLOOKUP tenvS l = some st ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)),
        store_assign l sv store_ = some store' ∧
        type_s ctMap_ store' tenvS := by
  intro ctMap_ tenvS store_ sv st l ⟨hs, hl, hsv⟩
  obtain ⟨sv0, h0, hsv0⟩ := type_s_lookup hs hl
  have hlt : l < store_.length := store_lookup_some_iff.1 ⟨_, h0⟩
  have hel : EL l store_ = sv0 := by
    unfold store_lookup at h0; simp [hlt] at h0; exact h0
  have hsame : store_v_same_type sv0 sv = true := by
    cases sv0 <;> cases sv <;> cases st <;> simp_all [type_sv, store_v_same_type]
  refine ⟨LUPDATE sv l store_, by simp [store_assign, hlt, hel, hsame], fun l' => ⟨?_, ?_⟩⟩
  · rw [(hs l').1, store_lookup_some_iff, store_lookup_some_iff]; simp [LUPDATE]
  · intro st' sv' ⟨h1, h2⟩
    by_cases he : l' = l
    · subst he
      unfold store_lookup at h2
      simp [LUPDATE, hlt, EL] at h2
      rw [hl] at h1; cases h1; subst h2; exact hsv
    · apply (hs l').2 st' sv' ⟨h1, ?_⟩
      unfold store_lookup at h2 ⊢
      simp only [LUPDATE, List.length_set] at h2
      split at h2
      · simp only [EL] at h2 ⊢
        rw [if_pos (by assumption)]
        have hne : l ≠ l' := Ne.symm he
        first
          | simpa [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne] using h2
          | simpa [getElem!_def, List.getElem?_set_ne hne] using h2
          | simpa [hne] using h2
      · cases h2
/- HOL4:
Theorem store_alloc_type_sound:
  !ctMap tenvS store sv st.
    ctMap_ok ctMap ∧
    type_s ctMap store tenvS ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store' tenvS' n.
      store_type_extension tenvS tenvS' ∧
      store_alloc sv store = (store', n) ∧
      type_s ctMap store' tenvS' ∧
      FLOOKUP tenvS' n = SOME st
-/
theorem store_alloc_type_sound :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t),
      ctMap_ok ctMap_ ∧
      type_s ctMap_ store_ tenvS ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)) (tenvS' : tenv_store) (n : Nat),
        store_type_extension tenvS tenvS' ∧
        store_alloc sv store_ = (store', n) ∧
        type_s ctMap_ store' tenvS' ∧
        Finmap.FLOOKUP tenvS' n = some st := by
  intro ctMap_ tenvS store_ sv st ⟨_, hs, hsv⟩
  have hdom : ∀ l, (∃ st', tenvS l = some st') ↔ l < store_.length := fun l =>
    ((hs l).1).trans store_lookup_some_iff
  have hnone : tenvS store_.length = none := by
    cases h : tenvS store_.length with
    | none => rfl
    | some x => exact absurd ((hdom _).1 ⟨x, h⟩) (Nat.lt_irrefl _)
  let ext : tenv_store := Finmap.FUPDATE Finmap.FEMPTY (store_.length, st)
  have hweak : weakS (Finmap.FUNION ext tenvS) tenvS := by
    intro k x hk
    simp only [Finmap.FUNION, ext, Finmap.FUPDATE, Finmap.FEMPTY]
    by_cases hk' : k = store_.length
    · subst hk'; rw [hnone] at hk; cases hk
    · simp [hk', hk]
  refine ⟨store_ ++ [sv], Finmap.FUNION ext tenvS, store_.length,
    ⟨ext, rfl, fun l => ?_⟩, rfl, fun l => ⟨?_, ?_⟩, ?_⟩
  · by_cases hl : l = store_.length
    · subst hl; exact Or.inr hnone
    · left; simp [Finmap.FLOOKUP, ext, Finmap.FUPDATE, Finmap.FEMPTY, hl]
  · rw [store_lookup_some_iff]
    simp only [Finmap.FLOOKUP, Finmap.FUNION, ext, Finmap.FUPDATE, Finmap.FEMPTY, List.length_append,
      List.length_singleton]
    by_cases hl : l = store_.length
    · subst hl; simp
    · simp only [beq_iff_eq, hl, if_false]
      rw [hdom]; omega
  · intro st' sv' ⟨h1, h2⟩
    simp only [Finmap.FLOOKUP, Finmap.FUNION, ext, Finmap.FUPDATE, Finmap.FEMPTY] at h1
    unfold store_lookup at h2
    simp only [List.length_append, List.length_singleton] at h2
    split at h2
    · by_cases hl : l = store_.length
      · subst hl
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at h1
        subst h1
        simp [EL] at h2
        subst h2
        exact type_sv_weakening _ _ _ _ _ _ ⟨hsv, weakCT_refl _, hweak⟩
      · simp only [beq_iff_eq, hl, if_false] at h1
        have hlt : l < store_.length := by have := (hdom l).1 ⟨_, h1⟩; exact this
        have : store_lookup l store_ = some sv' := by
          unfold store_lookup; simp [hlt, EL] at h2 ⊢
          rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt] at h2
          simpa using h2
        exact type_sv_weakening _ _ _ _ _ _ ⟨(hs l).2 st' sv' ⟨h1, this⟩, weakCT_refl _, hweak⟩
    · cases h2
  · simp [Finmap.FLOOKUP, Finmap.FUNION, ext, Finmap.FUPDATE]
-- store_lookup_type_sound is commented out in HOL4 source

theorem v_to_list_cases {x : v} {xs : List v} (h : v_to_list x = some xs) :
    (xs = [] ∧ x = list_to_v []) ∨
    ∃ a l v2, xs = a :: l ∧
      x = .Conv (some (.TypeStamp (mlstring.strlit "::") list_type_num)) [a, v2] ∧
      v_to_list v2 = some l := by
  unfold v_to_list at h
  split at h
  · split at h
    · cases h; left; refine ⟨rfl, ?_⟩; simp_all [list_to_v]
    · cases h
  · split at h
    · split at h
      · cases h
      · cases h; right; refine ⟨_, _, _, rfl, ?_, ‹_›⟩; simp_all
    · cases h
  · cases h

/- HOL4:
Theorem type_v_list_to_v:
  !x xs t.
    type_v n ctMap tenvS x t ∧
    v_to_list x = SOME xs ⇒
    type_v n ctMap tenvS (list_to_v xs) t
-/
theorem type_v_list_to_v :
    ∀ (n : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (x : v) (xs : List v) (t : sem_t),
      type_v n ctMap_ tenvS x t ∧
      v_to_list x = some xs →
      type_v n ctMap_ tenvS (list_to_v xs) t := by
  intro n ctMap_ tenvS x xs
  induction xs generalizing x with
  | nil =>
    intro t ⟨ht, hx⟩
    rcases v_to_list_cases hx with ⟨-, rfl⟩ | ⟨a, l, v2, h, -, -⟩
    · exact ht
    · cases h
  | cons a l ih =>
    intro t ⟨ht, hx⟩
    rcases v_to_list_cases hx with ⟨h, -⟩ | ⟨a', l', v2, h, rfl, h2⟩
    · cases h
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h
      cases ht with
      | conv_some _ _ _ ts' tvs' _ ts ti stmp h1 h2' h3 h4 h5 =>
        refine .conv_some _ _ _ ts' tvs' _ ts ti _ h1 h2' (by simpa using h3) ?_ h5
        intro i hi


        match i, hi with
        | 0, _ => exact h4 0 (by simp)
        | 1, _ => exact ih v2 _ ⟨h4 1 (by simp), h2⟩
/- HOL4:
Theorem type_v_list_to_v_APPEND:
  !xs ys t.
    ctMap_has_lists ctMap ∧
    type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) ∧
    type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
    ⇒
    type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num)
-/
theorem type_v_list_to_v_APPEND :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (xs ys : List v) (t : sem_t),
      ctMap_has_lists ctMap_ ∧
      type_v 0 ctMap_ tenvS (list_to_v xs) (.Tapp [t] Tlist_num) ∧
      type_v 0 ctMap_ tenvS (list_to_v ys) (.Tapp [t] Tlist_num) →
      type_v 0 ctMap_ tenvS (list_to_v (xs ++ ys)) (.Tapp [t] Tlist_num) := by
  intro ctMap_ tenvS xs ys t ⟨hl, hx, hy⟩
  induction xs with
  | nil => exact hy
  | cons a xs ih =>
    simp only [list_to_v, List.cons_append] at hx ⊢
    cases hx with
    | conv_some _ _ _ ts' tvs' _ ts ti stmp h1 h2 h3 h4 h5 =>
      rw [hl.2.1] at h5
      obtain ⟨rfl, rfl, -⟩ := Prod.mk.inj (Option.some.inj h5)
      have key : ∀ i, i < 2 → type_v 0 ctMap_ tenvS ([a, list_to_v xs])[i]!
          (([.Tvar (mlstring.strlit "'a"), Tlist (.Tvar (mlstring.strlit "'a"))] : List sem_t).map
            (type_subst (Finmap.FUPDATE_LIST Finmap.FEMPTY ([mlstring.strlit "'a"].zip [t]).reverse)))[i]! := by
        intro i hi; exact h4 i (by simpa using hi)
      have e1 : type_subst (Finmap.FUPDATE_LIST Finmap.FEMPTY ([mlstring.strlit "'a"].zip [t]).reverse)
          (Tlist (.Tvar (mlstring.strlit "'a"))) = .Tapp [t] Tlist_num := by
        simp [Tlist, type_subst, Finmap.FUPDATE_LIST, Finmap.FUPDATE, Finmap.FLOOKUP]
      have hxs := key 1 (by decide)
      simp only [List.map, e1] at hxs
      refine .conv_some _ _ _ [t] _ _ _ _ _ h1 h2 (by simp) ?_ hl.2.1
      intro i hi
      match i, hi with
      | 0, _ => exact key 0 (by decide)
      | 1, _ => simp only [List.map, e1]; exact ih hxs
/- HOL4:
Theorem do_eq_Boolv:
  do_eq (Boolv b) (Boolv b') = Eq_val (b = b')
-/
theorem do_eq_Boolv :
    ∀ (b b' : Bool),
      do_eq (Boolv b) (Boolv b') = .Eq_val (b == b') := by
  intro b b'
  cases b <;> cases b' <;> simp [Boolv, do_eq, do_eq_list, ctor_same_type, same_type]
/- HOL4:
Theorem prim_canonical_Boolv_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
  (∃b. v = Boolv b))
-/
theorem prim_canonical_Boolv_thm :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v),
      type_v tvs ctMap_ tenvS val_ Tbool ∧ ctMap_ok ctMap_ ∧ ctMap_has_bools ctMap_ →
      ∃ (b : Bool), val_ = Boolv b := by
  intro tvs ctMap_ tenvS val_ ⟨h, hok, hb⟩
  generalize hT : Tbool = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  rename_i hvl _ hl _
  obtain ⟨rfl, rfl⟩ := hT
  obtain ⟨hst, rfl, rfl⟩ := ctMap_bool_stamp hok hb hl
  have : _ = [] := List.eq_nil_of_length_eq_zero (by simpa using hvl)
  subst this
  rcases hst with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
/- HOL4:
Theorem prim_canonical_Boolv_cases[local]:
  type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ⇒
  v = Boolv T ∨ v = Boolv F
-/
theorem prim_canonical_Boolv_cases :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v),
      type_v tvs ctMap_ tenvS val_ (.Tapp [] Tbool_num) ∧
      ctMap_ok ctMap_ ∧
      ctMap_has_bools ctMap_ →
      val_ = Boolv true ∨ val_ = Boolv false := by
  intro tvs ctMap_ tenvS val_ ⟨h, hok, hb⟩
  obtain ⟨b, rfl⟩ := prim_canonical_Boolv_thm tvs ctMap_ tenvS val_ ⟨h, hok, hb⟩
  cases b <;> simp
theorem LIST_REL_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs1 xs2 : List α} {ys1 ys2 : List β},
      LIST_REL R xs1 ys1 → LIST_REL R xs2 ys2 → LIST_REL R (xs1 ++ xs2) (ys1 ++ ys2)
  | _, _, _, _, .nil, h2 => h2
  | _, _, _, _, .cons _ _ _ _ hr h1, h2 => .cons _ _ _ _ hr (LIST_REL_append h1 h2)

theorem LIST_REL_reverse {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, LIST_REL R xs ys → LIST_REL R xs.reverse ys.reverse
  | _, _, .nil => .nil
  | _, _, .cons _ _ _ _ hr h => by
    simp only [List.reverse_cons]
    exact LIST_REL_append (LIST_REL_reverse h) (.cons _ _ _ _ hr .nil)

theorem LIST_REL_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, LIST_REL R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ _ _ _ h => by simp [LIST_REL_length h]

theorem LIST_REL_getElem_bang {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, LIST_REL R xs ys →
      ∀ i, i < xs.length → R xs[i]! ys[i]!
  | _, _, .nil, i, hi => by simp at hi
  | _, _, .cons _ _ _ _ hr h, i, hi => by
    cases i with
    | zero => simpa using hr
    | succ i => simpa using LIST_REL_getElem_bang h i (by simpa using hi)

theorem LIST_REL_of_getElem_bang {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ i, i < xs.length → R xs[i]! ys[i]!) → LIST_REL R xs ys
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hl, h => .cons _ _ _ _ (by simpa using h 0 (by simp))
      (LIST_REL_of_getElem_bang (by simpa using hl) (fun i hi => by
        simpa using h (i + 1) (by simpa using hi)))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem type_v_Ttup_canonical {tvs : Nat} {ctMap_ : ctMap} {tenvS : tenv_store} {val_ : v}
    {ts : List sem_t} (hok : ctMap_ok ctMap_) (h : type_v tvs ctMap_ tenvS val_ (Ttup ts)) :
    ∃ vs, val_ = .Conv none vs ∧ LIST_REL (type_v tvs ctMap_ tenvS) vs ts := by
  generalize hT : Ttup ts = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  rename_i vs ts0 hl hv
  obtain ⟨rfl, -⟩ := hT
  exact ⟨vs, rfl, LIST_REL_of_getElem_bang hl hv⟩

theorem type_v_Tapp_ctor_canonical {tvs : Nat} {ctMap_ : ctMap} {tenvS : tenv_store} {val_ : v}
    {ts' : List sem_t} {tn : type_ident} {stmp : stamp} {tvs0 : List tvarN} {ts0 : List sem_t}
    (hok : ctMap_ok ctMap_) (hl : Finmap.FLOOKUP ctMap_ stmp = some (tvs0, ts0, tn))
    (h : type_v tvs ctMap_ tenvS val_ (.Tapp ts' tn)) :
    ∃ stmp' tvs'' ts'' vs, val_ = .Conv (some stmp') vs ∧
      Finmap.FLOOKUP ctMap_ stmp' = some (tvs'', ts'', tn) ∧
      tvs''.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs
        (ts''.map (type_subst (Finmap.alist_to_fmap (tvs''.zip ts')))) := by
  generalize hT : sem_t.Tapp ts' tn = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  · rename_i ts1 tvs1 vs1 tss1 ti1 st1 _ _ _ _ _
    obtain ⟨rfl, rfl⟩ := hT
    refine ⟨st1, tvs1, tss1, vs1, rfl, ‹_›, ‹_›, ?_⟩
    rw [← FUPDATE_LIST_reverse_eq_alist]
    exact LIST_REL_of_getElem_bang ‹_› ‹_›
  all_goals first
    | (obtain ⟨_, rfl⟩ := hT; exact absurd (ctMap_ok_prim_lookup hok hl (by decide)) (by decide))
    | (obtain ⟨rfl, rfl⟩ := hT; exact absurd (ctMap_ok_prim_lookup hok hl (by decide)) (by decide))
    | skip

/-- Typing of the result of a primitive operation. -/
def op_res_ok (ctMap_ : ctMap) (tenvS : tenv_store) (t : sem_t) : result v v → Prop
  | .Rval val_ => type_v 0 ctMap_ tenvS val_ t
  | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS val_ Texn
  | .Rerr (.Rabort (.Rffi_error _)) => True
  | .Rerr (.Rabort _) => False

/-- The conclusion of `op_type_sound`, for arguments given in evaluation order. -/
def OpOK {ffi : Type} (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
    (ffi_ : ffi_state ffi) (op_ : op) (us : List v) (t : sem_t) : Prop :=
  ∃ (tenvS' : tenv_store) (store' : List (store_v v)) (ffi' : ffi_state ffi)
    (r : result v v),
    store_type_extension tenvS tenvS' ∧
    type_s ctMap_ store' tenvS' ∧
    do_app (store_, ffi_) op_ us = some ((store', ffi'), r) ∧
    op_res_ok ctMap_ tenvS' t r

theorem OpOK_of_eq {ffi : Type} {ctMap_ : ctMap} {tenvS : tenv_store} {store_ : List (store_v v)}
    {ffi_ : ffi_state ffi} {op_ : op} {us : List v} {t : sem_t} {r : result v v}
    (hs : type_s ctMap_ store_ tenvS)
    (h : do_app (store_, ffi_) op_ us = some ((store_, ffi_), r))
    (hr : op_res_ok ctMap_ tenvS t r) : OpOK ctMap_ tenvS store_ ffi_ op_ us t :=
  ⟨tenvS, store_, ffi_, r, store_type_extension_refl _, hs, h, hr⟩

theorem OpOK_val {ffi : Type} {ctMap_ : ctMap} {tenvS : tenv_store} {store_ : List (store_v v)}
    {ffi_ : ffi_state ffi} {op_ : op} {us : List v} {t : sem_t} {w : v}
    (hs : type_s ctMap_ store_ tenvS)
    (h : do_app (store_, ffi_) op_ us = some ((store_, ffi_), .Rval w))
    (hw : type_v 0 ctMap_ tenvS w t) : OpOK ctMap_ tenvS store_ ffi_ op_ us t :=
  ⟨tenvS, store_, ffi_, _, store_type_extension_refl _, hs, h, hw⟩

theorem OpOK_raise {ffi : Type} {ctMap_ : ctMap} {tenvS : tenv_store} {store_ : List (store_v v)}
    {ffi_ : ffi_state ffi} {op_ : op} {us : List v} {t : sem_t} {w : v}
    (hs : type_s ctMap_ store_ tenvS)
    (h : do_app (store_, ffi_) op_ us = some ((store_, ffi_), .Rerr (.Rraise w)))
    (hw : type_v 0 ctMap_ tenvS w Texn) : OpOK ctMap_ tenvS store_ ffi_ op_ us t :=
  ⟨tenvS, store_, ffi_, _, store_type_extension_refl _, hs, h, hw⟩

theorem cv_int {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tint) : ∃ n, w = .Litv (.IntLit n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).1 ⟨h, hok⟩
theorem cv_char {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tchar) : ∃ n, w = .Litv (.Char n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).2.1 ⟨h, hok⟩
theorem cv_str {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tstring) : ∃ n, w = .Litv (.StrLit n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).2.2.1 ⟨h, hok⟩
theorem cv_w8 {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tword8) : ∃ n, w = .Litv (.Word8 n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).2.2.2.1 ⟨h, hok⟩
theorem cv_w64 {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tword64) : ∃ n, w = .Litv (.Word64 n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).2.2.2.2.1 ⟨h, hok⟩
theorem cv_double {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} (hok : ctMap_ok c)
    (h : type_v tvs c s w Tdouble) : ∃ n, w = .Litv (.Float64 n) :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint Tint).2.2.2.2.2.1 ⟨h, hok⟩
theorem cv_vector {tvs : Nat} {c : ctMap} {s : tenv_store} {w : v} {t : sem_t} (hok : ctMap_ok c)
    (h : type_v tvs c s w (Tvector t)) :
    ∃ vs, w = .Vectorv vs ∧ ∀ x, x ∈ vs → type_v tvs c s x t :=
  (prim_canonical_values_thm tvs c s w [] [] Tint Tint t).2.2.2.2.2.2.2.2.2.2.2 ⟨h, hok⟩
theorem cv_ref {tvs : Nat} {c : ctMap} {s : tenv_store} {st : List (store_v v)} {w : v}
    {t : sem_t} (hok : ctMap_ok c) (hs : type_s c st s)
    (h : type_v tvs c s w (Tref t)) :
    ∃ n v2, w = .Loc true n ∧ store_lookup n st = some (.Refv v2) ∧
      type_v 0 c s v2 t ∧ Finmap.FLOOKUP s n = some (.Ref_t t) ∧ check_freevars 0 [] t := by
  generalize hT : Tref t = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  rename_i t' n hfv hl
  obtain ⟨⟨rfl, -⟩, -⟩ := hT
  obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
  cases sv <;> simp only [type_sv] at h2
  exact ⟨_, _, rfl, h1, h2, hl, hfv⟩
theorem cv_w8array {tvs : Nat} {c : ctMap} {s : tenv_store} {st : List (store_v v)} {w : v}
    (hok : ctMap_ok c) (hs : type_s c st s)
    (h : type_v tvs c s w Tword8array) :
    ∃ n ws, w = .Loc true n ∧ store_lookup n st = some (.W8array ws) ∧
      Finmap.FLOOKUP s n = some .W8array_t :=
  (prim_canonical_values_thm tvs c s w st [] Tint Tint Tint).2.2.2.2.2.2.2.2.2.1 ⟨h, hok, hs⟩
theorem cv_array {tvs : Nat} {c : ctMap} {s : tenv_store} {st : List (store_v v)} {w : v}
    {t : sem_t} (hok : ctMap_ok c) (hs : type_s c st s)
    (h : type_v tvs c s w (Tarray t)) :
    ∃ n vs, w = .Loc true n ∧ store_lookup n st = some (.Varray vs) ∧
      (∀ x, x ∈ vs → type_v 0 c s x t) ∧ Finmap.FLOOKUP s n = some (.Varray_t t) ∧
      check_freevars 0 [] t := by
  generalize hT : Tarray t = T at h
  cases h <;> (try tv_unfold) <;> tv_close
  rename_i t' n hfv hl
  obtain ⟨⟨rfl, -⟩, -⟩ := hT
  obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
  cases sv <;> simp only [type_sv] at h2
  exact ⟨_, _, rfl, h1, h2, hl, hfv⟩

theorem type_v_list_to_v_of_all {tvs : Nat} {ctMap_ : ctMap} {tenvS : tenv_store} {t : sem_t}
    (hl : ctMap_has_lists ctMap_) (hfv : check_freevars tvs [] t) :
    ∀ (xs : List v), (∀ x, x ∈ xs → type_v tvs ctMap_ tenvS x t) →
      type_v tvs ctMap_ tenvS (list_to_v xs) (Tlist t)
  | [], _ => by
    refine .conv_some _ _ _ [t] _ [] [] _ _ (by simpa using hfv) rfl (by simp) (by simp) hl.1
  | a :: xs, h => by
    have e1 : type_subst (Finmap.FUPDATE_LIST Finmap.FEMPTY ([mlstring.strlit "'a"].zip [t]).reverse)
        (Tlist (.Tvar (mlstring.strlit "'a"))) = Tlist t := by
      simp [Tlist, type_subst, Finmap.FUPDATE_LIST, Finmap.FUPDATE, Finmap.FLOOKUP]
    have e0 : type_subst (Finmap.FUPDATE_LIST Finmap.FEMPTY ([mlstring.strlit "'a"].zip [t]).reverse)
        (.Tvar (mlstring.strlit "'a")) = t := by
      simp [type_subst, Finmap.FUPDATE_LIST, Finmap.FUPDATE, Finmap.FLOOKUP]
    refine .conv_some _ _ _ [t] _ [a, list_to_v xs] _ _ _ (by simpa using hfv) rfl (by simp) ?_ hl.2.1
    intro i hi
    match i, hi with
    | 0, _ => simp only [List.map, e0]; exact h a (by simp)
    | 1, _ => simp only [List.map, e1]; exact type_v_list_to_v_of_all hl hfv xs (fun x hx => h x (by simp [hx]))

theorem EL_mem_of_lt {α : Type} [Inhabited α] {n : Nat} {l : List α} (h : n < l.length) :
    EL n l ∈ l := by
  simp only [EL, getElem!_pos l n h]; exact List.getElem_mem h

theorem mem_LUPDATE_imp {α : Type} {x y : α} {n : Nat} {l : List α} (h : x ∈ LUPDATE y n l) :
    x = y ∨ x ∈ l := by
  simp only [LUPDATE] at h
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem mem_REPLICATE_imp {α : Type} {x y : α} {n : Nat} (h : x ∈ REPLICATE n y) : x = y := by
  simp only [REPLICATE, List.mem_replicate] at h; exact h.2

theorem v_beq_eq (a b : v) : (a == b) = v_beq a b := rfl

theorem check_type_Boolv (b : Bool) : check_type .BoolT (Boolv b) = true := by
  cases b <;> simp [check_type, Boolv, v_beq_eq, v_beq, v_list_beq]

set_option hygiene false in
macro "arith_fin" : tactic => `(tactic| (
  apply OpOK_of_eq hs
  · simp [do_app, do_arith, EVERY, check_type, check_type_Boolv, the_Litv_Float64,
      the_Litv_IntLit, the_Litv_Word8, the_Litv_Word64] <;> rfl
  · first | constructor | exact type_v_Boolv _ _ _ _ hg.2.1))

set_option hygiene false in
macro "op_destr" : tactic => `(tactic| (rcases hrel with _ | ⟨u1, t1, _, _, h1, _ | ⟨u2, t2, _, _, h2,
    _ | ⟨u3, t3, _, _, h3, _ | ⟨u4, t4, _, _, h4, _ | ⟨u5, t5, _, _, h5, hrest⟩⟩⟩⟩⟩) <;>
    simp only [type_op] at hty)

theorem op_type_sound_core {ffi : Type} (ctMap_ : ctMap) (tenvS : tenv_store)
    (store_ : List (store_v v)) (ffi_ : ffi_state ffi)
    (hg : good_ctMap ctMap_) (hs : type_s ctMap_ store_ tenvS) :
    ∀ (op_ : op) (ts : List sem_t) (t : sem_t) (us : List v),
      op_ ≠ .Opapp → type_op op_ ts t → check_freevars 0 [] t →
      LIST_REL (type_v 0 ctMap_ tenvS) us ts →
      OpOK ctMap_ tenvS store_ ffi_ op_ us t := by
  intro op_ ts t us hne hty hfv hrel
  have hsub : type_v 0 ctMap_ tenvS sub_exn_v Texn := (type_v_exn 0 ctMap_ tenvS hg.2.2.1).2.1
  cases op_
  case Arith a ty =>
    simp only [type_op] at hty
    obtain ⟨hall, rfl, hsa⟩ := hty
    rcases hrel with _ | ⟨u1, t1, _, _, h1, _ | ⟨u2, t2, _, _, h2,
      _ | ⟨u3, t3, _, _, h3, hrest⟩⟩⟩
    · cases ty <;> cases a <;> simp [supported_arith] at hsa
    · have e1 := hall t1 (by simp)
      subst e1
      rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> cases a <;> simp [supported_arith] at hsa <;>
        simp only [t_of] at h1 ⊢
      all_goals first
        | (obtain ⟨w1, rfl⟩ := cv_double hg.1 h1)
        | (obtain ⟨b1, rfl⟩ := prim_canonical_Boolv_thm _ _ _ _ ⟨h1, hg.1, hg.2.1⟩)
      all_goals first
        | arith_fin
        | skip
      refine OpOK_val hs ?_ (type_v_Boolv _ _ _ (!(the_Boolv (Boolv b1))) hg.2.1)
      simp [do_app, do_arith, EVERY, check_type_Boolv]
    · have e1 := hall t1 (by simp)
      have e2 := hall t2 (by simp)
      subst e1 e2
      rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> cases a <;> simp [supported_arith] at hsa <;>
        simp only [t_of] at h1 h2 ⊢
      all_goals first
        | (obtain ⟨w1, rfl⟩ := cv_double hg.1 h1; obtain ⟨w2, rfl⟩ := cv_double hg.1 h2)
        | (obtain ⟨w1, rfl⟩ := cv_int hg.1 h1; obtain ⟨w2, rfl⟩ := cv_int hg.1 h2)
        | (obtain ⟨w1, rfl⟩ := cv_w8 hg.1 h1; obtain ⟨w2, rfl⟩ := cv_w8 hg.1 h2)
        | (obtain ⟨w1, rfl⟩ := cv_w64 hg.1 h1; obtain ⟨w2, rfl⟩ := cv_w64 hg.1 h2)
      all_goals first
        | arith_fin
        | skip
      all_goals
        by_cases hw : w2 = 0
        · apply OpOK_of_eq hs
          · simp [do_app, do_arith, EVERY, check_type, the_Litv_IntLit, hw] <;> rfl
          · exact (type_v_exn 0 ctMap_ tenvS hg.2.2.1).2.2.2
        · apply OpOK_of_eq hs
          · simp [do_app, do_arith, EVERY, check_type, the_Litv_IntLit, hw] <;> rfl
          · constructor
    · have e1 := hall t1 (by simp)
      have e2 := hall t2 (by simp)
      have e3 := hall t3 (by simp)
      subst e1 e2 e3
      cases hrest
      · rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> cases a <;> simp [supported_arith] at hsa <;>
          simp only [t_of] at h1 h2 h3 ⊢
        obtain ⟨w1, rfl⟩ := cv_double hg.1 h1
        obtain ⟨w2, rfl⟩ := cv_double hg.1 h2
        obtain ⟨w3, rfl⟩ := cv_double hg.1 h3
        arith_fin
      · rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> cases a <;> simp [supported_arith] at hsa
  case FromTo ty1 ty2 =>
    op_destr
    obtain ⟨rfl, rfl, hsc⟩ := hty
    rcases ty1 with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> rcases ty2 with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;>
      simp [supported_conversion] at hsc <;> simp only [t_of] at h1 hfv ⊢
    all_goals first
      | obtain ⟨w, rfl⟩ := cv_int hg.1 h1
      | obtain ⟨w, rfl⟩ := cv_char hg.1 h1
      | obtain ⟨w, rfl⟩ := cv_w8 hg.1 h1
      | obtain ⟨w, rfl⟩ := cv_w64 hg.1 h1
      | obtain ⟨w, rfl⟩ := cv_double hg.1 h1
    all_goals first
      | (apply OpOK_of_eq hs
         · simp [do_app, check_type, do_conversion] <;> rfl
         · constructor)
      | skip
    by_cases hw : w < 0 ∨ 255 < w
    · apply OpOK_of_eq hs
      · simp [do_app, check_type, do_conversion, the_Litv_IntLit, hw] <;> rfl
      · exact (type_v_exn 0 ctMap_ tenvS hg.2.2.1).1
    · apply OpOK_of_eq hs
      · simp [do_app, check_type, do_conversion, the_Litv_IntLit, hw] <;> rfl
      · constructor
  case Shift ws sh n =>
    cases ws <;> op_destr
    · obtain ⟨rfl, rfl⟩ := hty
      obtain ⟨w, rfl⟩ := cv_w8 hg.1 h1
      refine OpOK_val hs ?_ (.litv_word8 _ _ _ (shift8_lookup sh w n)); simp [do_app]
    · obtain ⟨rfl, rfl⟩ := hty
      obtain ⟨w, rfl⟩ := cv_w64 hg.1 h1
      refine OpOK_val hs ?_ (.litv_word64 _ _ _ (shift64_lookup sh w n)); simp [do_app]
  case Equality =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    have hne' := eq_same_type_v 0 ctMap_ tenvS hg.1 _ u1 u2 t1 (Nat.lt_succ_self _) h1 h2
    cases hd : do_eq u1 u2 with
    | Eq_type_error => exact absurd hd hne'
    | Eq_val b => refine OpOK_val hs ?_ (type_v_Boolv _ _ _ b hg.2.1); simp [do_app, hd]
  case Test tst ty =>
    op_destr
    obtain ⟨rfl, rfl, rfl, hst⟩ := hty
    have hne' : do_test tst ty u1 u2 ≠ .Eq_type_error := by
      cases tst <;> simp [supported_test] at hst
      · rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [t_of] at h1 h2
        · obtain ⟨b1, rfl⟩ := prim_canonical_Boolv_thm _ _ _ _ ⟨h1, hg.1, hg.2.1⟩
          obtain ⟨b2, rfl⟩ := prim_canonical_Boolv_thm _ _ _ _ ⟨h2, hg.1, hg.2.1⟩
          simp [do_test, check_type_Boolv, do_eq_Boolv]
        all_goals first
          | (obtain ⟨w1, rfl⟩ := cv_int hg.1 h1; obtain ⟨w2, rfl⟩ := cv_int hg.1 h2)
          | (obtain ⟨w1, rfl⟩ := cv_char hg.1 h1; obtain ⟨w2, rfl⟩ := cv_char hg.1 h2)
          | (obtain ⟨w1, rfl⟩ := cv_str hg.1 h1; obtain ⟨w2, rfl⟩ := cv_str hg.1 h2)
          | (obtain ⟨w1, rfl⟩ := cv_w8 hg.1 h1; obtain ⟨w2, rfl⟩ := cv_w8 hg.1 h2)
          | (obtain ⟨w1, rfl⟩ := cv_w64 hg.1 h1; obtain ⟨w2, rfl⟩ := cv_w64 hg.1 h2)
          | (obtain ⟨w1, rfl⟩ := cv_double hg.1 h1; obtain ⟨w2, rfl⟩ := cv_double hg.1 h2)
        all_goals simp [do_test, check_type, do_eq, lit_same_type]
      · rcases hst with rfl | rfl | rfl | rfl <;> simp only [t_of] at h1 h2
        · obtain ⟨w1, rfl⟩ := cv_int hg.1 h1; obtain ⟨w2, rfl⟩ := cv_int hg.1 h2
          simp [do_test, dest_Litv]
        · obtain ⟨w1, rfl⟩ := cv_char hg.1 h1; obtain ⟨w2, rfl⟩ := cv_char hg.1 h2
          simp [do_test, dest_Litv]
        · obtain ⟨w1, rfl⟩ := cv_w8 hg.1 h1; obtain ⟨w2, rfl⟩ := cv_w8 hg.1 h2
          simp [do_test, dest_Litv]
        · obtain ⟨w1, rfl⟩ := cv_double hg.1 h1; obtain ⟨w2, rfl⟩ := cv_double hg.1 h2
          simp [do_test, dest_Litv]
    cases hd : do_test tst ty u1 u2 with
    | Eq_type_error => exact absurd hd hne'
    | Eq_val b => refine OpOK_val hs ?_ (type_v_Boolv _ _ _ b hg.2.1); simp [do_app, hd]
  case Opapp => exact absurd rfl hne
  case Opassign =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨n, v2, rfl, hlk, hv2, hfl, -⟩ := cv_ref hg.1 hs h1
    obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_ (.Refv u2) _ n
      ⟨hs, hfl, h2⟩
    refine ⟨tenvS, st', ffi_, .Rval (.Conv none []), store_type_extension_refl _, hs', by simp [do_app, has], ?_⟩
    exact .conv_none _ _ _ [] [] rfl (by simp)
  case Opref =>
    op_destr
    subst hty
    obtain ⟨st', tenvS', n, hext, halloc, hs', hl⟩ :=
      store_alloc_type_sound ctMap_ tenvS store_ (.Refv u1) (.Ref_t t1) ⟨hg.1, hs, h1⟩
    refine ⟨tenvS', st', ffi_, .Rval (.Loc true n), hext, hs', by simp [do_app, halloc], ?_⟩
    exact .loc_ref _ _ _ _ _ (by simpa [Tref, check_freevars] using hfv) hl
  case Opderef =>
    op_destr
    subst hty
    obtain ⟨n, v2, rfl, hlk, hv2, -⟩ := cv_ref hg.1 hs h1
    exact OpOK_val hs (by simp [do_app, hlk]) hv2
  case Aw8alloc =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨i, rfl⟩ := cv_int hg.1 h1
    obtain ⟨w, rfl⟩ := cv_w8 hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi]
    · obtain ⟨st', tenvS', n, hext, halloc, hs', hl⟩ :=
        store_alloc_type_sound ctMap_ tenvS store_ (.W8array (REPLICATE i.natAbs w)) .W8array_t
          ⟨hg.1, hs, trivial⟩
      refine ⟨tenvS', st', ffi_, .Rval (.Loc true n), hext, hs', by simp [do_app, hi, halloc], ?_⟩
      exact .loc_w8array _ _ _ _ hl
  case Aw8sub =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨n, ws, rfl, hlk, -⟩ := cv_w8array hg.1 hs h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk]
    by_cases hn : i.natAbs ≥ ws.length
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk, hn]
    · refine OpOK_val hs ?_ (.litv_word8 _ _ _ (EL i.natAbs ws)); simp [do_app, hi, hlk, hn]
  case Aw8length =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨n, ws, rfl, hlk, -⟩ := cv_w8array hg.1 hs h1
    refine OpOK_val hs ?_ (.litv_int _ _ _ (Int.ofNat ws.length)); simp [do_app, hlk]
  case Aw8update =>
    op_destr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hty
    obtain ⟨n, ws, rfl, hlk, hfl⟩ := cv_w8array hg.1 hs h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    obtain ⟨w, rfl⟩ := cv_w8 hg.1 h3
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk]
    by_cases hn : i.natAbs ≥ ws.length
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk, hn]
    · obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_
        (.W8array (LUPDATE w i.natAbs ws)) _ n ⟨hs, hfl, trivial⟩
      refine ⟨tenvS, st', ffi_, .Rval (.Conv none []), store_type_extension_refl _, hs',
        by simp [do_app, hi, hlk, hn, has], ?_⟩
      exact .conv_none _ _ _ [] [] rfl (by simp)
  case CopyStrStr =>
    op_destr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hty
    obtain ⟨str, rfl⟩ := cv_str hg.1 h1
    obtain ⟨off, rfl⟩ := cv_int hg.1 h2
    obtain ⟨len, rfl⟩ := cv_int hg.1 h3
    cases hc : copy_array (explode str, off) len none with
    | none => refine OpOK_raise hs ?_ hsub; simp [do_app, hc]
    | some cs =>
      refine OpOK_val hs ?_ (.litv_str _ _ _ (implode (String.ofList cs))); simp [do_app, hc] <;> rfl
  case CopyStrAw8 =>
    op_destr
    cases hrest <;> simp only at hty
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hty
    obtain ⟨str, rfl⟩ := cv_str hg.1 h1
    obtain ⟨off, rfl⟩ := cv_int hg.1 h2
    obtain ⟨len, rfl⟩ := cv_int hg.1 h3
    obtain ⟨n, ws, rfl, hlk, hfl⟩ := cv_w8array hg.1 hs h4
    obtain ⟨doff, rfl⟩ := cv_int hg.1 h5
    cases hc : copy_array (explode str, off) len (some (ws_to_chars ws, doff)) with
    | none => refine OpOK_raise hs ?_ hsub; simp [do_app, hc, hlk]
    | some cs =>
      obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_
        (.W8array (chars_to_ws cs)) _ n ⟨hs, hfl, trivial⟩
      refine ⟨tenvS, st', ffi_, .Rval (.Conv none []), store_type_extension_refl _, hs',
        by simp [do_app, hc, hlk, has], ?_⟩
      exact .conv_none _ _ _ [] [] rfl (by simp)
  case CopyAw8Str =>
    op_destr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hty
    obtain ⟨n, ws, rfl, hlk, hfl⟩ := cv_w8array hg.1 hs h1
    obtain ⟨off, rfl⟩ := cv_int hg.1 h2
    obtain ⟨len, rfl⟩ := cv_int hg.1 h3
    cases hc : copy_array (ws, off) len none with
    | none => refine OpOK_raise hs ?_ hsub; simp [do_app, hc, hlk]
    | some cs =>
      refine OpOK_val hs ?_ (.litv_str _ _ _ (implode (String.ofList (ws_to_chars cs))))
      simp [do_app, hc, hlk] <;> rfl
  case CopyAw8Aw8 =>
    op_destr
    cases hrest <;> simp only at hty
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hty
    obtain ⟨n, ws, rfl, hlk, hfl⟩ := cv_w8array hg.1 hs h1
    obtain ⟨off, rfl⟩ := cv_int hg.1 h2
    obtain ⟨len, rfl⟩ := cv_int hg.1 h3
    obtain ⟨m, ds, rfl, hlk', hfl'⟩ := cv_w8array hg.1 hs h4
    obtain ⟨doff, rfl⟩ := cv_int hg.1 h5
    cases hc : copy_array (ws, off) len (some (ds, doff)) with
    | none => refine OpOK_raise hs ?_ hsub; simp [do_app, hc, hlk, hlk']
    | some cs =>
      obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_
        (.W8array cs) _ m ⟨hs, hfl', trivial⟩
      refine ⟨tenvS, st', ffi_, .Rval (.Conv none []), store_type_extension_refl _, hs',
        by simp [do_app, hc, hlk, hlk', has], ?_⟩
      exact .conv_none _ _ _ [] [] rfl (by simp)
  case Implode =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨vs, -, -, hc, -⟩ := (ctor_canonical_values_thm 0 ctMap_ tenvS u1 Tchar [] 0
      default [] []).2.1 ⟨h1, hg.1, hg.2.2.2⟩
    obtain ⟨cs, hcs⟩ := hc rfl
    refine OpOK_val hs ?_ (.litv_str _ _ _ (implode (String.ofList cs))); simp [do_app, hcs] <;> rfl
  case Explode =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨str, rfl⟩ := cv_str hg.1 h1
    refine OpOK_val hs ?_ (type_v_list_to_v_of_all hg.2.2.2 (by simp [Tchar])
      ((explode str).map (fun c => .Litv (.Char c))) ?_)
    · simp [do_app]
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨c, -, rfl⟩ := hx
      exact .litv_char _ _ _ _
  case Strsub =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨str, rfl⟩ := cv_str hg.1 h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi]
    by_cases hn : i.natAbs ≥ strlen str
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hn]
    · refine OpOK_val hs ?_ (.litv_char _ _ _ (EL i.natAbs (explode str))); simp [do_app, hi, hn]
  case Strlen =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨str, rfl⟩ := cv_str hg.1 h1
    refine OpOK_val hs ?_ (.litv_int _ _ _ (Int.ofNat (strlen str))); simp [do_app]
  case Strcat =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨vs, hvs, -, -, hc⟩ := (ctor_canonical_values_thm 0 ctMap_ tenvS u1 Tstring [] 0
      default [] []).2.1 ⟨h1, hg.1, hg.2.2.2⟩
    obtain ⟨str, hstr⟩ := hc rfl
    refine OpOK_val hs ?_ (.litv_str _ _ _ str); simp [do_app, hvs, hstr]
  case VfromList =>
    op_destr
    rcases t1 with _ | _ | ⟨_ | ⟨a, _ | _⟩, ctor⟩ <;> simp only at hty
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨vs, hvs, hall, -⟩ := (ctor_canonical_values_thm 0 ctMap_ tenvS u1 a [] 0
      default [] []).2.1 ⟨h1, hg.1, hg.2.2.2⟩
    refine OpOK_val hs ?_ (.vectorv _ _ _ _ vs (by simpa [Tvector] using hfv) hall)
    simp [do_app, hvs]
  case Vsub =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨vs, rfl, hall⟩ := cv_vector hg.1 h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi]
    by_cases hn : i.natAbs ≥ vs.length
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hn]
    · refine OpOK_val hs ?_ (hall _ (EL_mem_of_lt (n := i.natAbs) (by omega))); simp [do_app, hi, hn]
  case Vlength =>
    op_destr
    rcases t1 with _ | _ | ⟨_ | ⟨a, _ | _⟩, ctor⟩ <;> simp only at hty
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨vs, rfl, -⟩ := cv_vector (t := a) hg.1 h1
    refine OpOK_val hs ?_ (.litv_int _ _ _ (Int.ofNat vs.length)); simp [do_app]
  case Aalloc =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨i, rfl⟩ := cv_int hg.1 h1
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi]
    · obtain ⟨st', tenvS', n, hext, halloc, hs', hl⟩ :=
        store_alloc_type_sound ctMap_ tenvS store_ (.Varray (REPLICATE i.natAbs u2)) (.Varray_t t2)
          ⟨hg.1, hs, fun x hx => by rw [mem_REPLICATE_imp hx]; exact h2⟩
      refine ⟨tenvS', st', ffi_, .Rval (.Loc true n), hext, hs', by simp [do_app, hi, halloc], ?_⟩
      exact .loc_varray _ _ _ _ _ (by simpa [Tarray] using hfv) hl
  case AallocEmpty =>
    op_destr
    obtain ⟨rfl, t2, rfl⟩ := hty
    obtain ⟨vs, rfl, hvs⟩ := type_v_Ttup_canonical hg.1 h1
    cases hvs
    obtain ⟨st', tenvS', n, hext, halloc, hs', hl⟩ :=
      store_alloc_type_sound ctMap_ tenvS store_ (.Varray []) (.Varray_t t2)
        ⟨hg.1, hs, fun x hx => by simp at hx⟩
    refine ⟨tenvS', st', ffi_, .Rval (.Loc true n), hext, hs', by simp [do_app, halloc], ?_⟩
    exact .loc_varray _ _ _ _ _ (by simpa [Tarray] using hfv) hl
  case Asub =>
    op_destr
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨n, vs, rfl, hlk, hall, -⟩ := cv_array hg.1 hs h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk]
    by_cases hn : i.natAbs ≥ vs.length
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk, hn]
    · refine OpOK_val hs ?_ (hall _ (EL_mem_of_lt (n := i.natAbs) (by omega))); simp [do_app, hi, hlk, hn]
  case Alength =>
    op_destr
    rcases t1 with _ | _ | ⟨_ | ⟨a, _ | _⟩, ctor⟩ <;> simp only at hty
    obtain ⟨rfl, rfl⟩ := hty
    obtain ⟨n, vs, rfl, hlk, -⟩ := cv_array (t := a) hg.1 hs h1
    refine OpOK_val hs ?_ (.litv_int _ _ _ (Int.ofNat vs.length)); simp [do_app, hlk]
  case Aupdate =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨n, vs, rfl, hlk, hall, hfl, -⟩ := cv_array hg.1 hs h1
    obtain ⟨i, rfl⟩ := cv_int hg.1 h2
    by_cases hi : i < 0
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk]
    by_cases hn : i.natAbs ≥ vs.length
    · refine OpOK_raise hs ?_ hsub; simp [do_app, hi, hlk, hn]
    · obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_
        (.Varray (LUPDATE u3 i.natAbs vs)) _ n ⟨hs, hfl, fun x hx => by
          rcases mem_LUPDATE_imp hx with rfl | hx
          · exact h3
          · exact hall x hx⟩
      refine ⟨tenvS, st', ffi_, .Rval (.Conv none []), store_type_extension_refl _, hs',
        by simp [do_app, hi, hlk, hn, has], ?_⟩
      exact .conv_none _ _ _ [] [] rfl (by simp)
  case ListAppend =>
    op_destr
    rcases t1 with _ | _ | ⟨_ | ⟨a, _ | _⟩, ctor⟩ <;> simp only at hty
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨xs, hxs, -⟩ := (ctor_canonical_values_thm 0 ctMap_ tenvS u1 a [] 0
      default [] []).2.1 ⟨h1, hg.1, hg.2.2.2⟩
    obtain ⟨ys, hys, -⟩ := (ctor_canonical_values_thm 0 ctMap_ tenvS u2 a [] 0
      default [] []).2.1 ⟨h2, hg.1, hg.2.2.2⟩
    refine OpOK_val hs ?_ (type_v_list_to_v_APPEND ctMap_ tenvS xs ys a ⟨hg.2.2.2,
      type_v_list_to_v _ _ _ _ _ _ ⟨h1, hxs⟩, type_v_list_to_v _ _ _ _ _ _ ⟨h2, hys⟩⟩)
    simp [do_app, hxs, hys]
  case ConfigGC =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨i, rfl⟩ := cv_int hg.1 h1
    obtain ⟨j, rfl⟩ := cv_int hg.1 h2
    refine OpOK_val hs ?_ (.conv_none _ _ _ [] [] rfl (by simp)); simp [do_app]
  case FFI fname =>
    op_destr
    obtain ⟨rfl, rfl, rfl⟩ := hty
    obtain ⟨conf, rfl⟩ := cv_str hg.1 h1
    obtain ⟨n, ws, rfl, hlk, hfl⟩ := cv_w8array hg.1 hs h2
    cases hc : call_FFI ffi_ (.ExtCall fname) ((explode conf).map (fun c => n2w_8 (ORD c))) ws with
    | FFI_return ffi' ws' =>
      obtain ⟨st', has, hs'⟩ := store_assign_type_sound ctMap_ tenvS store_
        (.W8array ws') _ n ⟨hs, hfl, trivial⟩
      refine ⟨tenvS, st', ffi', .Rval (.Conv none []), store_type_extension_refl _, hs',
        by simp [do_app, hc, hlk, has], ?_⟩
      exact .conv_none _ _ _ [] [] rfl (by simp)
    | FFI_final outcome =>
      exact ⟨tenvS, store_, ffi_, .Rerr (.Rabort (.Rffi_error outcome)), store_type_extension_refl _,
        hs, by simp [do_app, hc, hlk], trivial⟩
  all_goals op_destr

/- HOL4:
Theorem op_type_sound:
 !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
   good_ctMap ctMap ∧
   op ≠ Opapp ∧
   type_s ctMap store tenvS ∧
   type_op op ts t ∧
   check_freevars 0 [] t ∧
   LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort(Rffi_error _)) => T
   | Rerr (Rabort _) => F
-/
theorem op_type_sound :
    ∀ {ffi : Type} (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v)
      (op_ : op) (ts : List sem_t) (t : sem_t) (store_ : List (store_v v))
      (ffi_ : ffi_state ffi),
      good_ctMap ctMap_ ∧
      op_ ≠ .Opapp ∧
      type_s ctMap_ store_ tenvS ∧
      type_op op_ ts t ∧
      check_freevars 0 [] t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts.reverse →
      ∃ (tenvS' : tenv_store) (store' : List (store_v v)) (ffi' : ffi_state ffi)
        (r : result v v),
        store_type_extension tenvS tenvS' ∧
        type_s ctMap_ store' tenvS' ∧
        do_app (store_, ffi_) op_ vs.reverse = some ((store', ffi'), r) ∧
        match r with
        | .Rval val_ => type_v 0 ctMap_ tenvS' val_ t
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort _) => False := by
  intro ffi ctMap_ tenvS vs op_ ts t store_ ffi_ ⟨hg, hne, hs, hty, hfv, hrel⟩
  have hrel' := LIST_REL_reverse hrel
  rw [List.reverse_reverse] at hrel'
  obtain ⟨tenvS', store', ffi', r, h1, h2, h3, h4⟩ :=
    op_type_sound_core ctMap_ tenvS store_ ffi_ hg hs op_ ts t vs.reverse hne hty hfv hrel'
  refine ⟨tenvS', store', ffi', r, h1, h2, h3, ?_⟩
  rcases r with _ | (_ | (_ | _ | _)) <;> exact h4
/- HOL4:
Theorem build_conv_type_sound:
 !envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' tn)
-/
theorem build_conv_type_sound :
    ∀ (envC : env_ctor) (cn : cml_id modN conN) (vs : List v) (tvs : Nat)
      (ts : List sem_t) (ctMap_ : ctMap) (tenvS : tenv_store) (ts' : List sem_t)
      (tn : type_ident) (tenvC : tenv_ctor) (tvs' : List tvarN)
      (tenvE : tenv_val_exp) (l : Nat),
      nsAll2 (type_ctor ctMap_) envC tenvC ∧
      do_con_check envC (some cn) l ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs
        (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))).reverse ∧
      nsLookup tenvC cn = some (tvs', ts, tn) →
      ∃ (val_ : v),
        build_conv envC (some cn) vs.reverse = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (.Tapp ts' tn) := by
  intro envC cn vs tvs ts ctMap_ tenvS ts' tn tenvC tvs' tenvE l
    ⟨hall, _, h0, hfv, hlen, hrel, hl⟩
  obtain ⟨⟨k, st⟩, h1, h2, h3⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, hall⟩
  refine ⟨.Conv (some st) vs.reverse, by simp [build_conv, h1], ?_⟩
  have hrel' := LIST_REL_reverse hrel
  rw [List.reverse_reverse, ← FUPDATE_LIST_reverse_eq_alist] at hrel'
  refine .conv_some _ _ _ _ _ _ _ _ _ ?_ hlen (LIST_REL_length hrel')
    (LIST_REL_getElem_bang hrel') h2
  intro t' ht'
  simp only [EVERY, List.all_eq_true] at hfv
  have := hfv t' ht'
  rwa [bind_tvar_rewrites.2.1, h0, Nat.add_zero] at this
/- HOL4:
Theorem same_ctor_and_same_tid:
   !stamp1 stamp2.
    same_ctor stamp1 stamp2 ∧
    same_type stamp1 stamp2
    ⇒
    stamp1 = stamp2
-/
theorem same_ctor_and_same_tid :
    ∀ (stamp1 stamp2 : stamp),
      same_ctor stamp1 stamp2 ∧ same_type stamp1 stamp2 →
      stamp1 = stamp2 := by
  intro s1 s2 ⟨h, _⟩
  simpa [same_ctor] using h
mutual
theorem pat_type_sound_p {cenv : env_ctor} {st : store v} {ctMap_ : ctMap} {tenvS : tenv_store}
    (hok : ctMap_ok ctMap_) (hs : type_s ctMap_ st tenvS) :
    ∀ {tvs : Nat} {tenv : type_env} {p : pat} {t : sem_t} {nb : List (varN × sem_t)},
    type_p tvs tenv p t nb → nsAll2 (type_ctor ctMap_) cenv tenv.c →
    ∀ (val_ : v) (bindings : List (varN × v)) (tbindings : List (varN × sem_t)),
      type_v tvs ctMap_ tenvS val_ t →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch cenv st p val_ bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch cenv st p val_ bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings' (nb ++ tbindings)
  | _, _, _, _, _, .pany _ _ _ _, _, val_, b, tb, _, hb => Or.inr ⟨b, by simp [pmatch], hb⟩
  | _, _, _, _, _, .pvar _ _ n _ _, _, val_, b, tb, hv, hb =>
    Or.inr ⟨(n, val_) :: b, by simp [pmatch], .cons _ _ _ _ ⟨rfl, hv⟩ hb⟩
  | _, _, _, _, _, .plit_int _ _ _, _, val_, b, tb, hv, hb => by
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm _ _ _ _ st [] Tint Tint Tint).1 ⟨hv, hok⟩
    simp only [pmatch]; split
    · exact Or.inr ⟨b, rfl, hb⟩
    · simp [lit_same_type]
  | _, _, _, _, _, .plit_char _ _ _, _, val_, b, tb, hv, hb => by
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm _ _ _ _ st [] Tint Tint Tint).2.1 ⟨hv, hok⟩
    simp only [pmatch]; split
    · exact Or.inr ⟨b, rfl, hb⟩
    · simp [lit_same_type]
  | _, _, _, _, _, .plit_str _ _ _, _, val_, b, tb, hv, hb => by
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm _ _ _ _ st [] Tint Tint Tint).2.2.1 ⟨hv, hok⟩
    simp only [pmatch]; split
    · exact Or.inr ⟨b, rfl, hb⟩
    · simp [lit_same_type]
  | _, _, _, _, _, .plit_word8 _ _ _, _, val_, b, tb, hv, hb => by
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm _ _ _ _ st [] Tint Tint Tint).2.2.2.1 ⟨hv, hok⟩
    simp only [pmatch]; split
    · exact Or.inr ⟨b, rfl, hb⟩
    · simp [lit_same_type]
  | _, _, _, _, _, .plit_word64 _ _ _, _, val_, b, tb, hv, hb => by
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm _ _ _ _ st [] Tint Tint Tint).2.2.2.2.1 ⟨hv, hok⟩
    simp only [pmatch]; split
    · exact Or.inr ⟨b, rfl, hb⟩
    · simp [lit_same_type]
  | _, _, _, _, _, .pcon_some _ _ cn ps ts' tvs' ts tn _ _ hlen hps hl, hc, val_, b, tb, hv, hb => by
    obtain ⟨_, stmp, hcl, hfl⟩ := (type_env_conv_thm _ _ _ hc cn tvs' ts tn tn).1 hl
    obtain ⟨stmp', tvs'', ts'', vs, rfl, hfl', hlen', hvs⟩ :=
      type_v_Tapp_ctor_canonical hok hfl hv
    have hst := hok.2.2.2 _ _ _ _ _ _ _ ⟨hfl, hfl'⟩
    have hpl := type_ps_length_aux hps
    simp only [List.length_map] at hpl
    simp only [pmatch, hcl, hst, hpl, beq_self_eq_true, Bool.and_self, if_true]
    split
    · rename_i hsc
      have : stmp = stmp' := by simpa [same_ctor] using hsc
      subst this
      rw [hfl] at hfl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hfl'
      obtain ⟨rfl, rfl, -⟩ := hfl'
      have hvl := LIST_REL_length hvs
      simp only [List.length_map] at hvl
      simp only [hvl, beq_self_eq_true, if_true]
      exact pat_type_sound_ps hok hs hps hc vs b tb hvs hb
    · exact Or.inl rfl
  | _, _, _, _, _, .pcon_none _ _ ps ts _ hps, hc, val_, b, tb, hv, hb => by
    obtain ⟨vs, rfl, hvs⟩ := type_v_Ttup_canonical hok hv
    have hpl := type_ps_length_aux hps
    have hvl := LIST_REL_length hvs
    simp only [pmatch, hpl, hvl, beq_self_eq_true, if_true]
    exact pat_type_sound_ps hok hs hps hc vs b tb hvs hb
  | tvs, _, _, _, _, .pref _ _ p t _ hp, hc, val_, b, tb, hv, hb => by
    obtain ⟨n, v2, rfl, hsl, hv2⟩ :=
      (prim_canonical_values_thm _ _ _ _ st [] t Tint Tint).2.2.2.2.2.2.2.2.1 ⟨hv, hok, hs⟩
    have hv2' := type_v_weakening _ _ _ _ _ hv2 tvs ctMap_ tenvS ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩
    simp only [pmatch, hsl]
    exact pat_type_sound_p hok hs hp hc v2 b tb hv2' hb
  | _, _, _, _, _, .pas _ _ p t _ i hp, hc, val_, b, tb, hv, hb => by
    simp only [pmatch]
    rw [List.append_assoc]
    exact pat_type_sound_p hok hs hp hc val_ ((i, val_) :: b) ((i, t) :: tb) hv
      (.cons _ _ _ _ ⟨rfl, hv⟩ hb)
  | _, _, _, _, _, .ptannot _ _ p t _ _ _ hp, hc, val_, b, tb, hv, hb => by
    simp only [pmatch]
    exact pat_type_sound_p hok hs hp hc val_ b tb hv hb

theorem pat_type_sound_ps {cenv : env_ctor} {st : store v} {ctMap_ : ctMap} {tenvS : tenv_store}
    (hok : ctMap_ok ctMap_) (hs : type_s ctMap_ st tenvS) :
    ∀ {tvs : Nat} {tenv : type_env} {ps : List pat} {ts : List sem_t} {nb : List (varN × sem_t)},
    type_ps tvs tenv ps ts nb → nsAll2 (type_ctor ctMap_) cenv tenv.c →
    ∀ (vs : List v) (bindings : List (varN × v)) (tbindings : List (varN × sem_t)),
      LIST_REL (type_v tvs ctMap_ tenvS) vs ts →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch_list cenv st ps vs bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch_list cenv st ps vs bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings' (nb ++ tbindings)
  | _, _, _, _, _, .nil _ _, _, _, b, tb, .nil, hb => Or.inr ⟨b, by simp [pmatch_list], hb⟩
  | _, _, _, _, _, .cons _ _ p t _ ps ts _ hp hps, hc, _, b, tb, .cons v1 _ vs _ hv hvs, hb => by
    simp only [pmatch_list]
    rcases pat_type_sound_p hok hs hp hc v1 b tb hv hb with h1 | ⟨b1, h1, hb1⟩
    · rw [h1]
      rcases pat_type_sound_ps hok hs hps hc vs b tb hvs hb with h2 | ⟨b2, h2, _⟩
      · rw [h2]; exact Or.inl rfl
      · rw [h2]; exact Or.inl rfl
    · rw [h1]
      rw [List.append_assoc]
      exact pat_type_sound_ps hok hs hps hc vs b1 _ hvs hb1
end

/- HOL4:
Theorem pat_type_sound:
  (∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings)))
-/
theorem pat_type_sound :
    (∀ (cenv : env_ctor) (st : store v) (p : pat) (val_ : v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (t : sem_t)
       (new_tbindings : List (varN × sem_t)) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      type_v tvs ctMap_ tenvS val_ t ∧
      type_p tvs tenv p t new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch cenv st p val_ bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch cenv st p val_ bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) ∧
    (∀ (cenv : env_ctor) (st : store v) (ps : List pat) (vs : List v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (new_tbindings : List (varN × sem_t))
       (ts : List sem_t) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs ts ∧
      type_ps tvs tenv ps ts new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch_list cenv st ps vs bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch_list cenv st ps vs bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) := by
  refine ⟨fun cenv st p val_ b tenv ctMap_ tb t nb tenvS tvs ⟨hok, hc, hv, hp, hs, hb⟩ =>
    pat_type_sound_p hok hs hp hc val_ b tb hv hb,
    fun cenv st ps vs b tenv ctMap_ tb nb ts tenvS tvs ⟨hok, hc, hvs, hps, hs, hb⟩ =>
    pat_type_sound_ps hok hs hps hc vs b tb hvs hb⟩
/- HOL4:
Theorem lookup_var_sound:
   !n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)
-/
theorem lookup_var_sound :
    ∀ (n : cml_id modN varN) (tvs : Nat) (tenvE : tenv_val_exp)
      (targs : List sem_t) (t : sem_t) (ctMap_ : ctMap) (tenvS : tenv_store)
      (env : sem_env) (tenv : type_env),
      lookup_var n (bind_tvar tvs tenvE) tenv = some (targs.length, t) ∧
      ctMap_ok ctMap_ ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      ∃ (val_ : v),
        nsLookup env.v_ n = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (deBruijn_subst 0 targs t) := by
  intro n tvs tenvE targs t ctMap_ tenvS env tenv ⟨hl, hok, hEok, h0, hev, _, hv⟩
  have hlook : nsLookup (add_tenvE tenvE tenv.v) n = some (targs.length, t) := by
    unfold lookup_var at hl
    split at hl
    · rename_i x hx
      cases hl
      cases n with
      | Short y =>
        simp only [lookup_varE, tveLookup_bind_tvar, Nat.zero_add] at hx
        exact nsLookup_add_tenvE1 _ _ _ _ _ _
          ⟨tveLookup_closed y tenvE _ _ _ hEok h0 hx, hx⟩
      | Long _ _ => simp [lookup_varE] at hx
    · rename_i hx
      cases n with
      | Short y =>
        simp only [lookup_varE, tveLookup_bind_tvar, Nat.zero_add] at hx
        exact nsLookup_add_tenvE2 _ _ _ _ _ _ ⟨hx, hl⟩
      | Long mn y => exact nsLookup_add_tenvE3 _ _ _ _ _ _ hl
  obtain ⟨val_, h1, h2⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hlook, hv⟩
  refine ⟨val_, h1, ?_⟩
  exact type_subst_thm targs tvs _ _ _ _ _ h2
    ⟨rfl, hok, hev, type_v_freevars _ _ _ _ _ h2⟩
/- HOL4:
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t'))
-/
theorem EVERY_REPLICATE :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenv : tenv_store) (t' : sem_t) (vs : List v),
      (∀ (x : v), x ∈ vs → type_v tvs ctMap_ tenv x t') ↔
      (∀ (x : v × sem_t), x ∈ vs.zip (REPLICATE vs.length t') → type_v tvs ctMap_ tenv x.1 x.2) := by
  intro tvs ctMap_ tenv t' vs
  induction vs with
  | nil => simp [REPLICATE]
  | cons a l ih =>
    simp only [REPLICATE, List.length_cons, List.replicate_succ, List.zip_cons_cons,
      List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]
/- HOL4:
Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
-/
theorem EVERY_LIST_REL_thm :
    ∀ (n : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (t : sem_t) (vs : List v),
      (∀ (v_ : v), v_ ∈ vs → type_v n ctMap_ tenvS v_ t) ↔
      LIST_REL (type_v n ctMap_ tenvS) vs (REPLICATE vs.length t) := by
  intro n ctMap_ tenvS t vs
  exact EVERY_LIST_REL_local (fun x y => type_v n ctMap_ tenvS x y) t vs
