/-
  Translation of typeSoundScript.sml
  Proof of type soundness: a type-correct program does not crash.
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
      do_eq_list vs1 vs2 ≠ .Eq_type_error) := sorry
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
        | .Rerr (.Rabort _) => False := sorry
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
          (new_tbindings ++ tbindings)) := sorry
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
/- HOL4:
Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F)
-/
theorem exp_type_sound :
    ∀ (ctMap_ : ctMap),
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (es : List exp)
       (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env)
       (tenvE : tenv_val_exp) (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => LIST_REL (type_v tvs ctMap_ tenvS') vs ts
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) ∧
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (val_ : v)
       (pes : List (pat × exp)) (err_v : v) (r : result (List v) v)
       (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
       (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env val_ pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      type_v tvs ctMap_ tenvS val_ t1 ∧
      type_v 0 ctMap_ tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => type_v tvs ctMap_ tenvS' vs.head! t2
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) := sorry
theorem FUPDATE_LIST_reverse_apply {α β : Type} [BEq α] [LawfulBEq α] (m : Finmap α β) :
    ∀ (l : List (α × β)) (k : α),
      Finmap.FUPDATE_LIST m l.reverse k = (ALOOKUP l k).or (m k)
  | [], k => by simp [Finmap.FUPDATE_LIST, ALOOKUP]
  | (a, b) :: l, k => by
    have ih := FUPDATE_LIST_reverse_apply m l k
    simp only [Finmap.FUPDATE_LIST, List.reverse_cons, List.foldl_append, List.foldl] at ih ⊢
    simp only [Finmap.FUPDATE, ALOOKUP, ih]
    by_cases h : a = k
    · subst h; simp
    · have h' : k ≠ a := fun e => h e.symm
      simp [h, h']

theorem build_tdefs_no_mods (next : Nat) (tds : type_def) :
    ∃ L, build_tdefs next tds = .Bind L [] := by
  induction tds generalizing next with
  | nil => exact ⟨[], rfl⟩
  | cons td tds ih =>
    obtain ⟨_, _, ctors⟩ := td
    obtain ⟨L, hL⟩ := ih (next + 1)
    exact ⟨L ++ (build_constrs next ctors).reverse, by simp [build_tdefs, hL, nsAppend, alist_to_ns]⟩

theorem build_ctor_tenv_no_mods (tenvT : tenv_abbrev) :
    ∀ (tds : type_def) (tids : List type_ident),
    ∃ L, build_ctor_tenv tenvT tds tids = .Bind L []
  | [], [] => ⟨[], rfl⟩
  | (tvs, _, ctors) :: tds, id_ :: ids => by
    obtain ⟨L, hL⟩ := build_ctor_tenv_no_mods tenvT tds ids
    exact ⟨L ++ (ctors.map fun (p : conN × List ast_t) =>
        (p.1, (tvs, p.2.map (type_name_subst tenvT), id_))).reverse,
      by simp [build_ctor_tenv, hL, nsAppend, alist_to_ns]⟩
  | [], _ :: _ => ⟨[], rfl⟩
  | _ :: _, [] => ⟨[], rfl⟩

theorem nsLookup_nsAppend_alist_Short {α : Type} (X : «namespace» modN conN α)
    (Y : List (conN × α)) (cn : conN) :
    nsLookup (nsAppend X (alist_to_ns Y)) (.Short cn) = (nsLookup X (.Short cn)).or (ALOOKUP Y cn) := by
  cases X; simp [nsAppend, alist_to_ns, nsLookup, ALOOKUP_append]

theorem ALOOKUP_map_key {κ γ : Type} [BEq κ] (key : conN → κ) (f : conN × List ast_t → γ)
    (cn : conN) (hkey : ∀ a, (key a == key cn) = (a == cn)) :
    ∀ (l : List (conN × List ast_t)),
      ALOOKUP (l.map fun p => (key p.1, f p)) (key cn) = (l.find? (fun p => p.1 == cn)).map f
  | [] => rfl
  | (a, ts) :: l => by
    simp only [List.map_cons, ALOOKUP, List.find?_cons, hkey]
    cases h : (a == cn) <;> simp [ALOOKUP_map_key key f cn hkey l]

theorem build_tdefs_lookup_rel (tenvT : tenv_abbrev) :
    ∀ (tds : type_def) (tids : List type_ident) (next : Nat), tds.length = tids.length →
    (∀ cn, (nsLookup (build_tdefs next tds) (.Short cn) = none ∧
            nsLookup (build_ctor_tenv tenvT tds tids) (.Short cn) = none) ∨
      ∃ k st p, nsLookup (build_tdefs next tds) (.Short cn) = some (k, st) ∧
        nsLookup (build_ctor_tenv tenvT tds tids) (.Short cn) = some p ∧
        p.2.1.length = k ∧ ALOOKUP (type_def_to_ctMap tenvT next tds tids) st = some p) ∧
    (∀ st p, (st, p) ∈ type_def_to_ctMap tenvT next tds tids →
      ∃ cn j, st = .TypeStamp cn j ∧ next ≤ j)
  | [], [], next, _ => by
    refine ⟨fun cn => Or.inl ?_, fun st p h => by simp [type_def_to_ctMap] at h⟩
    simp [build_tdefs, build_ctor_tenv, alist_to_ns, nsLookup, ALOOKUP]
  | (tvs, tn, ctors) :: tds, id_ :: ids, next, hlen => by
    obtain ⟨ih1, ih2⟩ := build_tdefs_lookup_rel tenvT tds ids (next + 1) (by simpa using hlen)
    refine ⟨fun cn => ?_, fun st p h => ?_⟩
    · simp only [build_tdefs, build_ctor_tenv, type_def_to_ctMap, nsLookup_nsAppend_alist_Short,
        build_constrs, ← List.map_reverse, ALOOKUP_append]
      have e1 := ALOOKUP_map_key (fun c => c) (fun p => (p.2.length, stamp.TypeStamp p.1 next))
        cn (fun _ => rfl) ctors.reverse
      have e2 := ALOOKUP_map_key (fun c => c)
        (fun p => (tvs, p.2.map (type_name_subst tenvT), id_)) cn (fun _ => rfl) ctors.reverse
      have e3 := ALOOKUP_map_key (fun c => stamp.TypeStamp c next)
        (fun p => (tvs, p.2.map (type_name_subst tenvT), id_)) cn
        (fun a => by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, stamp.TypeStamp.injEq]; simp)
        ctors.reverse
      simp only at e1 e2 e3
      rcases ih1 cn with ⟨h1, h2⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h1, h2]
        simp only [Option.none_or]
        rw [e1, e2]
        have hnone : ALOOKUP (type_def_to_ctMap tenvT (next + 1) tds ids)
            (stamp.TypeStamp cn next) = none := by
          rw [ALOOKUP_none_iff]
          intro hm
          obtain ⟨⟨st, p⟩, hm, rfl⟩ := List.mem_map.1 hm
          obtain ⟨_, j, hj, hle⟩ := ih2 _ _ hm
          simp only [stamp.TypeStamp.injEq] at hj
          omega
        cases hf : List.find? (fun p => p.1 == cn) ctors.reverse with
        | none => left; simp
        | some q =>
          right
          refine ⟨_, _, _, rfl, rfl, by simp, ?_⟩
          have hq : q.1 = cn := by simpa using List.find?_some hf
          rw [hq, hnone, Option.none_or, e3, hf]; rfl
      · right
        refine ⟨k, st, p, by rw [h1]; rfl, by rw [h2]; rfl, h3, by rw [h4]; rfl⟩
    · simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h
      rcases h with h | ⟨q, _, hq⟩
      · obtain ⟨cn, j, hj, hle⟩ := ih2 st p h
        exact ⟨cn, j, hj, by omega⟩
      · simp only [Prod.mk.injEq] at hq
        exact ⟨q.1, next, hq.1.symm, Nat.le_refl _⟩
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/- HOL4:
Theorem build_tdefs_build_tenv[local]:
  !tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids)
-/
theorem build_tdefs_build_tenv :
    ∀ (tenvT : tenv_abbrev) (tds : type_def) (tids : List type_ident)
      (next : Nat) (ctMap_ : ctMap),
      EVERY (fun (p : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (p.2.2.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by
  intro tenvT tds tids next ctMap_ ⟨_, hlen⟩
  obtain ⟨hrel, _⟩ := build_tdefs_lookup_rel tenvT tds tids next hlen
  obtain ⟨L1, hL1⟩ := build_tdefs_no_mods next tds
  obtain ⟨L2, hL2⟩ := build_ctor_tenv_no_mods tenvT tds tids
  have hflook : ∀ st p, ALOOKUP (type_def_to_ctMap tenvT next tds tids) st = some p →
      Finmap.FLOOKUP (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse)
        st = some p := by
    intro st p h
    simp only [Finmap.FLOOKUP]
    rw [FUPDATE_LIST_reverse_apply, h]; rfl
  refine ⟨⟨fun id_ v1 h => ?_, fun path hp => ?_⟩, ⟨fun id_ v2 h => ?_, fun path hp => ?_⟩⟩
  · cases id_ with
    | Short cn =>
      rcases hrel cn with ⟨h1, _⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h1] at h; cases h
      · rw [h1] at h; cases h
        exact ⟨p, h2, hflook _ _ h4, h3⟩
    | Long mn i => rw [hL1] at h; simp [nsLookup, ALOOKUP] at h
  · cases path with
    | nil => simp [nsLookupMod] at hp
    | cons mn path => rw [hL1]; simp [nsLookupMod, ALOOKUP]
  · cases id_ with
    | Short cn =>
      rcases hrel cn with ⟨_, h2⟩ | ⟨k, st, p, h1, h2, h3, h4⟩
      · rw [h2] at h; cases h
      · rw [h2] at h; cases h
        exact ⟨(k, st), h1, hflook _ _ h4, h3⟩
    | Long mn i => rw [hL2] at h; simp [nsLookup, ALOOKUP] at h
  · cases path with
    | nil => simp [nsLookupMod] at hp
    | cons mn path => rw [hL2]; simp [nsLookupMod, ALOOKUP]
/- HOL4:
Theorem type_sound_invariant_union[local]:
  type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv
-/
theorem type_sound_invariant_union :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tids1 tids2 : Set type_ident) (tenv : type_env),
      type_sound_invariant st env ctMap_ tenvS (tids1 ∪ tids2) tenv →
      type_sound_invariant st env ctMap_ tenvS tids1 tenv := by
  intro ffi st env ctMap_ tenvS tids1 tids2 tenv ⟨h1, h2, ⟨h3, h3'⟩, h4, h5⟩
  exact ⟨h1, h2, ⟨fun x hx => h3 x ⟨Or.inl hx.1, hx.2⟩, h3'⟩, h4, h5⟩
/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds
-/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : tenv_abbrev) (tds : type_def),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by
  intro tenvT tds
  induction tds with
  | nil => intro; rfl
  | cons td tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := td
    intro h
    simp only [check_ctor_tenv, Bool.and_eq_true] at h
    simp only [EVERY, List.all_cons, Bool.and_eq_true] at ih ⊢
    exact ⟨h.1.1.1.1, ih h.2⟩
/- HOL4:
Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    ∧ type_all_env ctMap tenvS env2 tenv2
    ⇒ type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2)
-/
theorem type_all_env_extend :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (env1 env2 : sem_env)
      (tenv1 tenv2 : type_env),
      type_all_env ctMap_ tenvS env1 tenv1 ∧
      type_all_env ctMap_ tenvS env2 tenv2 →
      type_all_env ctMap_ tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) := by
  intro ctMap_ tenvS env1 env2 tenv1 tenv2 ⟨⟨h1, h2⟩, h3, h4⟩
  exact ⟨nsAll2_nsAppend _ _ _ _ _ ⟨h1, h3⟩, nsAll2_nsAppend _ _ _ _ _ ⟨h2, h4⟩⟩
/- HOL4:
Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs)
-/
theorem type_e_con_check :
    ∀ (ctMap_ : ctMap) (envc : env_ctor),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      every_exp (one_con_check envc) e) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env_ : List (varN × sem_t)),
      type_funs tenv tenvE funs env_ →
      nsAll2 (type_ctor ctMap_) envc tenv.c →
      EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs) := by
  intro ctMap_ envc
  have key : ∀ (tenv : type_env), nsAll2 (type_ctor ctMap_) envc tenv.c →
      (∀ {tenvE e t}, type_e tenv tenvE e t → every_exp (one_con_check envc) e) ∧
      (∀ {tenvE es ts}, type_es tenv tenvE es ts →
        ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es) ∧
      (∀ {tenvE funs env_}, type_funs tenv tenvE funs env_ →
        EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs) := by
    intro tenv hc
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    all_goals
      first
      | refine type_e.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
      | refine type_es.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
      | refine type_funs.rec
          (motive_1 := fun _ e _ _ => every_exp (one_con_check envc) e)
          (motive_2 := fun _ es ts _ => ts.length = es.length ∧ EVERY (every_exp (one_con_check envc)) es)
          (motive_3 := fun _ funs _ _ =>
            EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    all_goals (intros; try simp_all [every_exp, one_con_check, EVERY])
    all_goals first
      | assumption
      | simp [do_con_check]; done
      | (rename_i hl ih
         obtain ⟨⟨k, st⟩, h1, _, h3⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, hc⟩
         simp only at h3
         simp [do_con_check, h1, ← h3, ih.1])
  exact ⟨fun tenv _ _ _ h hc => (key tenv hc).1 h,
    fun tenv _ _ _ h hc => ((key tenv hc).2.1 h).2,
    fun tenv _ _ _ h hc => (key tenv hc).2.2 h⟩
/- HOL4:
Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T
-/
theorem decs_type_sound_no_check :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (st' : cml_state ffi) (r : result sem_env v) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True := sorry
/- HOL4:
Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
-/
theorem decs_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (extra_checks : Bool) (st' : cml_state ffi) (r : result sem_env v)
      (ctMap_ : ctMap) (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtimeout_error) => True := sorry
/- HOL4:
Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail
-/
theorem semantics_type_sound :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (tops : List dec)
      (r : behaviour) (checks : Bool) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      r ≠ .Fail := sorry
