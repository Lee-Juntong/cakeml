/-
  Translation of typeSysPropsScript.sml
  Theorems about the type system.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition type_pes_def:
  type_pes tvs tvs' tenv tenvE pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e tenv (bind_var_list tvs' bindings tenvE) e t2)
End
-/
def type_pes (tvs tvs' : Nat) (tenv : type_env) (tenvE : tenv_val_exp)
    (pes : List (pat × exp)) (t1 t2 : sem_t) : Prop :=
  ∀ pe, pe ∈ pes →
    ∃ bindings,
      ALL_DISTINCT (pat_bindings pe.1 []) ∧
      type_p tvs tenv pe.1 t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) pe.2 t2

/- HOL4:
Definition deBruijn_subst_tenvE_def:
(deBruijn_subst_tenvE targs Empty = Empty) ∧
(deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
  Bind_tvar tvs (deBruijn_subst_tenvE targs env)) ∧
(deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
  Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs)
                                  t)
       (deBruijn_subst_tenvE targs env))
End
-/
def deBruijn_subst_tenvE (targs : List sem_t) : tenv_val_exp → tenv_val_exp
  | .Empty => .Empty
  | .Bind_tvar tvs env => .Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | .Bind_name x tvs t env =>
    .Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env)
        (targs.map (deBruijn_inc 0 (tvs + num_tvs env))) t)
      (deBruijn_subst_tenvE targs env)

/- HOL4:
Definition db_merge_def:
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))
End
-/
def db_merge : tenv_val_exp → tenv_val_exp → tenv_val_exp
  | .Empty, e => e
  | .Bind_tvar tvs e1, e2 => .Bind_tvar tvs (db_merge e1 e2)
  | .Bind_name x tvs t e1, e2 => .Bind_name x tvs t (db_merge e1 e2)

/- HOL4:
Definition type_def_to_ctMap_def:
  (type_def_to_ctMap tenvT next_stamp [] [] = []) ∧
  (type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    REVERSE
      (MAP (\(cn,ts).
        (TypeStamp cn next_stamp, (tvs, MAP (type_name_subst tenvT) ts, id)))
        ctors))
End
-/
def type_def_to_ctMap (tenvT : tenv_abbrev) (next_stamp : Nat) :
    List (List tvarN × mlstring × List (conN × List ast_t)) →
    List type_ident → List (stamp × (List tvarN × List sem_t × type_ident))
  | [], [] => []
  | (tvs, _, ctors) :: tds, id_ :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    (ctors.map fun (cn, ts) =>
      (stamp.TypeStamp cn next_stamp, (tvs, ts.map (type_name_subst tenvT), id_))).reverse
  | _, _ => []

/- HOL4:
Definition tenv_names_def[simp]:
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)
End
-/
def tenv_names : tenv_val_exp → Set mlstring
  | .Empty => ∅
  | .Bind_tvar _ e => tenv_names e
  | .Bind_name n _ _ e => {n} ∪ tenv_names e

-- ============================================================
-- Theorem stubs
-- ============================================================

-- ============================================================
-- Auxiliary lemmas (not part of the HOL4 development)
-- ============================================================

theorem sem_t.ind' {P : sem_t → Prop}
    (hv : ∀ tv, P (.Tvar tv)) (hdb : ∀ n, P (.Tvar_db n))
    (happ : ∀ ts tn, (∀ t ∈ ts, P t) → P (.Tapp ts tn)) : ∀ t, P t
  | .Tvar tv => hv tv
  | .Tvar_db n => hdb n
  | .Tapp ts tn => happ ts tn (fun t _ => sem_t.ind' hv hdb happ t)

@[simp] theorem check_freevars_Tvar (dbmax : Nat) (tvs : List mlstring) (tv : mlstring) :
    check_freevars dbmax tvs (.Tvar tv) = tvs.any (· == tv) := by simp [check_freevars]

@[simp] theorem check_freevars_Tvar_db (dbmax : Nat) (tvs : List mlstring) (n : Nat) :
    check_freevars dbmax tvs (.Tvar_db n) = decide (n < dbmax) := by simp [check_freevars]

theorem list_map_eq_self {α : Type} {f : α → α} {l : List α} (h : ∀ x ∈ l, f x = x) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp at h; simp [h.1, ih h.2]

theorem EL_map' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (n : Nat)
    (h : n < l.length) : EL n (l.map f) = f (EL n l) := by
  simp [EL, h]

theorem EL_mem' {α : Type} [Inhabited α] (l : List α) (n : Nat) (h : n < l.length) :
    EL n l ∈ l := by
  simp [EL, h]

theorem alist_to_fmap_zip_map {α β : Type} [BEq α] (ks : List α) (vs : List β) (f : β → β)
    (k : α) :
    Finmap.alist_to_fmap (ZIP (ks, vs.map f)) k =
      (Finmap.alist_to_fmap (ZIP (ks, vs)) k).map f := by
  induction ks generalizing vs with
  | nil => simp [ZIP, Finmap.alist_to_fmap]
  | cons a ks ih =>
    cases vs with
    | nil => simp [ZIP, Finmap.alist_to_fmap]
    | cons b vs =>
      have := ih vs
      simp only [ZIP, Finmap.alist_to_fmap] at this ⊢
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      split <;> simp_all

theorem alist_to_fmap_zip_mem {α β : Type} [BEq α] (ks : List α) (vs : List β) (k : α) (x : β)
    (h : Finmap.alist_to_fmap (ZIP (ks, vs)) k = some x) : x ∈ vs := by
  induction ks generalizing vs with
  | nil => simp [ZIP, Finmap.alist_to_fmap] at h
  | cons a ks ih =>
    cases vs with
    | nil => simp [ZIP, Finmap.alist_to_fmap] at h
    | cons b vs =>
      simp only [ZIP, Finmap.alist_to_fmap, List.zip_cons_cons, List.find?_cons] at h
      split at h
      · simp at h; simp [h]
      · exact List.mem_cons_of_mem _ (ih vs h)

theorem alist_to_fmap_zip_isSome {α β : Type} [BEq α] [LawfulBEq α] (ks : List α) (vs : List β)
    (k : α) (hk : k ∈ ks) (hl : ks.length = vs.length) :
    ∃ x, Finmap.alist_to_fmap (ZIP (ks, vs)) k = some x := by
  induction ks generalizing vs with
  | nil => simp at hk
  | cons a ks ih =>
    cases vs with
    | nil => simp at hl
    | cons b vs =>
      simp only [ZIP, Finmap.alist_to_fmap, List.zip_cons_cons, List.find?_cons]
      split
      · simp
      · rename_i hne
        have hka : k ≠ a := by intro e; subst e; simp at hne
        simp [hka] at hk
        exact ih vs hk (by simpa using hl)

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv
-/
theorem unchanged_tenv :
    ∀ (tenv : type_env),
      { v := tenv.v, c := tenv.c, t := tenv.t : type_env} = tenv := fun _ => rfl
/- HOL4:
Theorem extend_dec_tenv_assoc[simp]:
   !tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3
-/
theorem extend_dec_tenv_assoc_thm :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3) =
      extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 := by
  intro tenv1 tenv2 tenv3
  simp [extend_dec_tenv, nsAppend_assoc]
/- HOL4:
Theorem tenv_val_ok_nsEmpty[simp]:
   tenv_val_ok nsEmpty
-/
theorem tenv_val_ok_nsEmpty :
    tenv_val_ok nsEmpty := nsAll_nsEmpty _
/- HOL4:
Theorem tenv_ctor_ok_nsEmpty[simp]:
   tenv_ctor_ok nsEmpty
-/
theorem tenv_ctor_ok_nsEmpty :
    tenv_ctor_ok nsEmpty := nsAll_nsEmpty _
/- HOL4:
Theorem tenv_abbrev_ok_nsEmpty[simp]:
   tenv_abbrev_ok nsEmpty
-/
theorem tenv_abbrev_ok_nsEmpty :
    tenv_abbrev_ok nsEmpty := nsAll_nsEmpty _
/- HOL4:
Theorem tenv_ok_empty[simp]:
   tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>
-/
theorem tenv_ok_empty :
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } := ⟨nsAll_nsEmpty _, nsAll_nsEmpty _, nsAll_nsEmpty _⟩
/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)
-/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := by
  intro tvs tvs' t
  induction t using sem_t.ind' with
  | hv => intros; simp_all
  | hdb => simp; omega
  | happ ts tn ih => simp; intro h k hk t ht; exact ih t ht (h t ht) k hk
/- HOL4:
Theorem check_freevars_subst_single:
 !dbmax tvs t tvs' ts.
  LENGTH tvs = LENGTH ts ∧
  check_freevars dbmax tvs t ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  check_freevars dbmax tvs' (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts))) t)
-/
theorem check_freevars_subst_single :
    ∀ (dbmax : Nat) (tvs : List tvarN) (t : sem_t) (tvs' : List tvarN) (ts : List sem_t),
      tvs.length = ts.length ∧
      check_freevars dbmax tvs t ∧
      EVERY (check_freevars dbmax tvs') ts →
      check_freevars dbmax tvs' (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))) t) := by
  intro dbmax tvs t tvs' ts ⟨hl, hc, hts⟩
  simp only [EVERY, List.all_eq_true] at hts
  induction t using sem_t.ind' with
  | hv tv =>
    simp at hc
    obtain ⟨x, hx⟩ := alist_to_fmap_zip_isSome tvs ts tv hc hl
    simp only [type_subst, Finmap.FLOOKUP, hx]
    exact hts x (alist_to_fmap_zip_mem _ _ _ _ hx)
  | hdb n => simpa [type_subst] using hc
  | happ ts' tn ih =>
    simp only [type_subst, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp] at hc ⊢
    intro t ht; exact ih t ht (hc t ht)
/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)
-/
theorem deBruijn_inc0 :
    (∀ (t : sem_t) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List sem_t) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := by
  have h : ∀ (t : sem_t) (sk : Nat), deBruijn_inc sk 0 t = t := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_inc]
    | hdb => simp [deBruijn_inc]
    | happ ts tn ih =>
      intro sk; simp only [deBruijn_inc, sem_t.Tapp.injEq, and_true]
      exact list_map_eq_self (fun t ht => ih t ht sk)
  exact ⟨h, fun ts sk => list_map_eq_self (fun t _ => h t sk)⟩
/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t
-/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by
  intro sk i2 t
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_inc]
  | hdb m =>
    intro i1
    by_cases h : m < sk
    · simp [deBruijn_inc, h]
    · simp [deBruijn_inc, h, show ¬ m + i2 < sk by omega]; omega
  | happ ts tn ih =>
    intro i1
    simp only [deBruijn_inc, List.map_map, sem_t.Tapp.injEq, and_true]
    exact List.map_congr_left (fun t ht => ih t ht i1)
/- HOL4: [local]
Theorem deBuijn_inc_lem1:
  !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t
-/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t := by
  intro sk i2 t
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_inc]
  | hdb m =>
    intro i1
    simp [deBruijn_inc, show ¬ m + (sk + i2) < sk by omega]; omega
  | happ ts tn ih =>
    intro i1
    simp only [deBruijn_inc, List.map_map, sem_t.Tapp.injEq, and_true]
    exact List.map_congr_left (fun t ht => ih t ht i1)
/- HOL4: [local]
Theorem type_subst_deBruijn_inc_single:
  !s t ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  (s = Finmap.alist_to_fmap (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (Finmap.alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t)
-/
theorem type_subst_deBruijn_inc_single :
    ∀ (s : Finmap tvarN sem_t) (t : sem_t) (ts : List sem_t) (tvs : List tvarN) (inc sk : Nat),
      tvs.length = ts.length ∧
      s = Finmap.alist_to_fmap (ZIP (tvs, ts)) ∧
      check_freevars 0 tvs t →
      deBruijn_inc sk inc (type_subst s t) =
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t)))) t := by
  intro s t ts tvs inc sk ⟨_, _, hc⟩
  subst s
  induction t using sem_t.ind' with
  | hv tv =>
    simp only [type_subst, Finmap.FLOOKUP, alist_to_fmap_zip_map]
    cases Finmap.alist_to_fmap (ZIP (tvs, ts)) tv <;> simp [deBruijn_inc]
  | hdb n => simp at hc
  | happ ts' tn ih =>
    simp only [check_freevars_Tapp, List.all_eq_true] at hc
    simp only [type_subst, deBruijn_inc, List.map_map, sem_t.Tapp.injEq, and_true]
    exact List.map_congr_left (fun t ht => ih t ht (hc t ht))
/- HOL4:
Theorem type_subst_deBruijn_inc_list:
 !ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts)))) ts') =
   MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts')
-/
theorem type_subst_deBruijn_inc_list :
    ∀ (ts' ts : List sem_t) (tvs : List tvarN) (inc sk : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts' →
      (ts'.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))))).map (deBruijn_inc sk inc) =
      ts'.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t))))) := by
  intro ts' ts tvs inc sk ⟨hl, hc⟩
  simp only [EVERY, List.all_eq_true] at hc
  simp only [List.map_map]
  exact List.map_congr_left (fun t ht =>
    type_subst_deBruijn_inc_single _ t ts tvs inc sk ⟨hl, rfl, hc t ht⟩)
/- HOL4: [local]
Theorem check_freevars_deBruijn_inc:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)
-/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by
  intro tvs tvs' t
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_inc]
  | hdb m =>
    intro h n n'
    simp at h
    by_cases hm : m < n' <;> simp [deBruijn_inc, hm] <;> omega
  | happ ts tn ih =>
    intro h n n'
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_inc, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp]
    intro t ht; exact ih t ht (h t ht) n n'
/- HOL4:
Theorem nil_deBruijn_inc:
 ∀skip tvs t.
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒
  (deBruijn_inc skip tvs t = t)
-/
theorem nil_deBruijn_inc :
    ∀ (skip tvs : Nat) (t : sem_t),
      (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t)) →
      deBruijn_inc skip tvs t = t := by
  intro skip tvs t
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_inc]
  | hdb m =>
    by_cases hm : m < skip <;> simp [deBruijn_inc, hm] <;> omega
  | happ ts tn ih =>
    intro h
    simp only [deBruijn_inc, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp] at h ⊢
    simp only [sem_t.Tapp.injEq, and_true]
    apply list_map_eq_self
    intro t ht
    rcases h with h | h
    · exact ih t ht (Or.inl (h t ht))
    · exact ih t ht (Or.inr (h t ht))
/- HOL4:
Theorem deBruijn_subst_check_freevars:
 !tvs tvs' t ts n.
  check_freevars tvs tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
-/
theorem deBruijn_subst_check_freevars :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t) (ts : List sem_t) (n : Nat),
      check_freevars tvs tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  intro tvs tvs' t ts _ ⟨hc, hts⟩
  simp only [EVERY, List.all_eq_true] at hts
  induction t using sem_t.ind' with
  | hv => simpa [deBruijn_subst] using hc
  | hdb m =>
    simp at hc
    by_cases hm : m < ts.length
    · simp [deBruijn_subst, hm]; exact hts _ (EL_mem' _ _ hm)
    · simp [deBruijn_subst, hm]; omega
  | happ ts' tn ih =>
    simp only [deBruijn_subst, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp] at hc ⊢
    intro t ht; exact ih t ht (hc t ht)
/- HOL4:
Theorem deBruijn_subst_check_freevars2:
 !tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
-/
theorem deBruijn_subst_check_freevars2 :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t) (ts : List sem_t) (n : Nat) (tvs'' : List tvarN),
      check_freevars ts.length tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  intro tvs tvs' t ts _ _ ⟨hc, hts⟩
  simp only [EVERY, List.all_eq_true] at hts
  induction t using sem_t.ind' with
  | hv => simpa [deBruijn_subst] using hc
  | hdb m =>
    simp at hc
    simp [deBruijn_subst, hc]; exact hts _ (EL_mem' _ _ hc)
  | happ ts' tn ih =>
    simp only [deBruijn_subst, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp] at hc ⊢
    intro t ht; exact ih t ht (hc t ht)
/- HOL4:
Theorem check_freevars_subst_inc:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2
     (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t))
-/
theorem check_freevars_subst_inc :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2
          (deBruijn_subst 0 targs (deBruijn_inc targs.length tvs1 t)) := by
  intro tvs tvs2 t
  induction t using sem_t.ind' with
  | hv => intro h _ _ _ _; simpa [deBruijn_subst, deBruijn_inc] using h
  | hdb m =>
    intro h tvs' targs tvs1 ⟨he, hts⟩
    simp only [EVERY, List.all_eq_true] at hts
    simp at h
    by_cases hm : m < targs.length
    · simp [deBruijn_inc, deBruijn_subst, hm]; exact hts _ (EL_mem' _ _ hm)
    · simp [deBruijn_inc, deBruijn_subst, hm, show ¬ m + tvs1 < targs.length by omega]; omega
  | happ ts tn ih =>
    intro h tvs' targs tvs1 hh
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_inc, deBruijn_subst, List.map_map, check_freevars_Tapp, List.all_map,
      List.all_eq_true, Function.comp]
    intro t ht; exact ih t ht (h t ht) tvs' targs tvs1 hh
/- HOL4:
Theorem check_freevars_subst:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t)
-/
theorem check_freevars_subst :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := by
  intro tvs tvs2 t
  induction t using sem_t.ind' with
  | hv => intro h _ _ _ _; simpa [deBruijn_subst] using h
  | hdb m =>
    intro h tvs' targs tvs1 ⟨he, hts⟩
    simp only [EVERY, List.all_eq_true] at hts
    simp at h
    by_cases hm : m < targs.length
    · simp [deBruijn_subst, hm]; exact hts _ (EL_mem' _ _ hm)
    · simp [deBruijn_subst, hm]; omega
  | happ ts tn ih =>
    intro h tvs' targs tvs1 hh
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_subst, check_freevars_Tapp, List.all_map,
      List.all_eq_true, Function.comp]
    intro t ht; exact ih t ht (h t ht) tvs' targs tvs1 hh
/- HOL4: [local]
Theorem type_subst_deBruijn_subst_single:
  !s t tvs tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars 0 tvs t ∧
  (s = Finmap.alist_to_fmap (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts))) t) =
   type_subst (Finmap.alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t)
-/
theorem type_subst_deBruijn_subst_single :
    ∀ (s : Finmap tvarN sem_t) (t : sem_t) (tvs : List tvarN) (tvs' : List tvarN)
      (ts ts' : List sem_t) (inc : Nat),
      tvs.length = ts.length ∧
      check_freevars 0 tvs t ∧
      s = Finmap.alist_to_fmap (ZIP (tvs, ts)) →
      deBruijn_subst inc ts' (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))) t) =
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t)))) t := by
  intro s t tvs _ ts ts' inc ⟨_, hc, _⟩
  induction t using sem_t.ind' with
  | hv tv =>
    simp only [type_subst, Finmap.FLOOKUP, alist_to_fmap_zip_map]
    cases Finmap.alist_to_fmap (ZIP (tvs, ts)) tv <;> simp [deBruijn_subst]
  | hdb n => simp at hc
  | happ ts'' tn ih =>
    simp only [check_freevars_Tapp, List.all_eq_true] at hc
    simp only [type_subst, deBruijn_subst, List.map_map, sem_t.Tapp.injEq, and_true]
    exact List.map_congr_left (fun t ht => ih t ht (hc t ht))
/- HOL4:
Theorem type_subst_deBruijn_subst_list:
 !t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')
-/
theorem type_subst_deBruijn_subst_list :
    ∀ (t_ : sem_t) (tvs : List tvarN) (tvs' : List tvarN)
      (ts ts' ts'' : List sem_t) (inc : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts'' →
      (ts''.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))))).map (deBruijn_subst inc ts') =
      ts''.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t))))) := by
  intro _ tvs tvs' ts ts' ts'' inc ⟨hl, hc⟩
  simp only [EVERY, List.all_eq_true] at hc
  simp only [List.map_map]
  exact List.map_congr_left (fun t ht =>
    type_subst_deBruijn_subst_single _ t tvs tvs' ts ts' inc ⟨hl, hc t ht, rfl⟩)
/- HOL4: [local]
Theorem check_freevars_lem:
  !l tvs' t.
  check_freevars l tvs' t ⇒
  !targs n1 tvs.
    (l = n1 + (LENGTH targs)) ∧
    EVERY (check_freevars tvs tvs') targs
     ⇒
     check_freevars (n1 + tvs) tvs'
       (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t)
-/
theorem check_freevars_lem :
    ∀ (l : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars l tvs' t →
      ∀ (targs : List sem_t) (n1 tvs : Nat),
        l = n1 + targs.length ∧
        EVERY (check_freevars tvs tvs') targs →
        check_freevars (n1 + tvs) tvs'
          (deBruijn_subst n1 (targs.map (deBruijn_inc 0 n1)) t) := by
  intro l tvs' t
  induction t using sem_t.ind' with
  | hv => intro h _ _ _ _; simpa [deBruijn_subst] using h
  | hdb m =>
    intro h targs n1 tvs ⟨he, hts⟩
    simp only [EVERY, List.all_eq_true] at hts
    simp at h
    by_cases hm : m < n1
    · simp [deBruijn_subst, hm]; omega
    · have hm2 : m - n1 < targs.length := by omega
      simp [deBruijn_subst, hm, show m < targs.length + n1 by omega]
      rw [EL_map' _ _ _ hm2]
      have := check_freevars_deBruijn_inc tvs tvs' _ (hts _ (EL_mem' _ _ hm2)) n1 0
      exact this
  | happ ts tn ih =>
    intro h targs n1 tvs hh
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_subst, check_freevars_Tapp, List.all_map,
      List.all_eq_true, Function.comp]
    intro t ht; exact ih t ht (h t ht) targs n1 tvs hh
/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)
-/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List sem_t) (t : sem_t),
      check_freevars skip [] t →
      deBruijn_subst skip tvs t = t := by
  intro skip tvs t
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_subst]
  | hdb m => intro h; simp at h; simp [deBruijn_subst, h]
  | happ ts tn ih =>
    intro h
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_subst, sem_t.Tapp.injEq, and_true]
    exact list_map_eq_self (fun t ht => ih t ht (h t ht))
/- HOL4:
Theorem deBruijn_subst2:
 (!t sk targs targs' tvs'.
  check_freevars (LENGTH targs) [] t ⇒
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
 (!ts sk targs targs' tvs'.
  EVERY (check_freevars (LENGTH targs) []) ts ⇒
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts)))
-/
theorem deBruijn_subst2_thm :
    (∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t) ∧
    (∀ (ts : List sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      EVERY (check_freevars targs.length []) ts →
      (ts.map (deBruijn_subst 0 targs)).map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
      ts.map (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have h1 : ∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_subst]
    | hdb m =>
      intro sk targs targs' _ h
      simp at h
      simp [deBruijn_subst, h]
      rw [EL_map' _ _ _ h]
    | happ ts tn ih =>
      intro sk targs targs' tvs' h
      simp only [check_freevars_Tapp, List.all_eq_true] at h
      simp only [deBruijn_subst, List.map_map, sem_t.Tapp.injEq, and_true]
      exact List.map_congr_left (fun t ht => ih t ht sk targs targs' tvs' (h t ht))
  refine ⟨h1, ?_⟩
  intro ts sk targs targs' tvs' h
  simp only [EVERY, List.all_eq_true] at h
  simp only [List.map_map]
  exact List.map_congr_left (fun t ht => h1 t sk targs targs' tvs' (h t ht))
/- HOL4:
Theorem type_e_subst_lem3:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs n.
  (tvs = n + LENGTH targs) ∧
  EVERY (check_freevars tvs' tvs2) targs
  ⇒
  check_freevars (n + tvs') tvs2
     (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t)
-/
theorem type_e_subst_lem3 :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (n : Nat),
        tvs = n + targs.length ∧
        EVERY (check_freevars tvs' tvs2) targs →
        check_freevars (n + tvs') tvs2
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) := by
  intro tvs tvs2 t h tvs' targs n hh
  exact check_freevars_lem tvs tvs2 t h targs n tvs' hh
/- HOL4: [local]
Theorem type_e_subst_lem5:
  (!t n inc n' targs.
   deBruijn_inc n inc
         (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
   deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs)
         (deBruijn_inc n inc t)) ∧
 (!ts n inc n' targs.
   MAP (deBruijn_inc n inc)
         (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
   MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
         (MAP (deBruijn_inc n inc) ts))
-/
theorem type_e_subst_lem5 :
    (∀ (t : sem_t) (n inc n' : Nat) (targs : List sem_t),
      deBruijn_inc n inc
        (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
      deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
        (deBruijn_inc n inc t)) ∧
    (∀ (ts : List sem_t) (n inc n' : Nat) (targs : List sem_t),
      (ts.map (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))))).map (deBruijn_inc n inc) =
      (ts.map (deBruijn_inc n inc)).map (deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n'))))) := by
  have h1 : ∀ (t : sem_t) (n inc n' : Nat) (targs : List sem_t),
      deBruijn_inc n inc
        (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
      deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
        (deBruijn_inc n inc t) := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_subst, deBruijn_inc]
    | hdb m =>
      intro n inc n' targs
      by_cases c1 : m < n
      · simp [deBruijn_subst, deBruijn_inc, c1, show m < n + n' by omega,
          show m < n + inc + n' by omega]
      by_cases c2 : m < n + n'
      · simp [deBruijn_subst, deBruijn_inc, c1, c2, show m + inc < n + inc + n' by omega]
      by_cases c3 : m < targs.length + (n + n')
      · have hk : m - (n + n') < targs.length := by omega
        simp [deBruijn_subst, deBruijn_inc, c1, c2, c3,
          show ¬ m + inc < n + inc + n' by omega,
          show m + inc < targs.length + (n + inc + n') by omega]
        rw [EL_map' _ _ _ hk, show m + inc - (n + inc + n') = m - (n + n') by omega,
          EL_map' _ _ _ hk]
        rw [show n + n' = n + n' from rfl]
        have := deBuijn_inc_lem1 n n' (EL (m - (n + n')) targs) inc
        rw [this]; congr 1; omega
      · simp [deBruijn_subst, deBruijn_inc, c1, c2, c3,
          show ¬ m + inc < n + inc + n' by omega,
          show ¬ m + inc < targs.length + (n + inc + n') by omega,
          show ¬ m - targs.length < n by omega]
        omega
    | happ ts tn ih =>
      intro n inc n' targs
      simp only [deBruijn_subst, deBruijn_inc, List.map_map, sem_t.Tapp.injEq, and_true]
      exact List.map_congr_left (fun t ht => ih t ht n inc n' targs)
  refine ⟨h1, ?_⟩
  intro ts n inc n' targs
  simp only [List.map_map]
  exact List.map_congr_left (fun t _ => h1 t n inc n' targs)
/- HOL4:
Theorem subst_inc_cancel:
 (!t ts inc.
  deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t)
  =
  deBruijn_inc 0 inc t) ∧
 (!ts' ts inc.
  MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts')
  =
  MAP (deBruijn_inc 0 inc) ts')
-/
theorem subst_inc_cancel :
    (∀ (t : sem_t) (ts : List sem_t) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) =
      deBruijn_inc 0 inc t) ∧
    (∀ (ts' ts : List sem_t) (inc : Nat),
      (ts'.map (deBruijn_inc 0 (inc + ts.length))).map (deBruijn_subst 0 ts) =
      ts'.map (deBruijn_inc 0 inc)) := by
  have h1 : ∀ (t : sem_t) (ts : List sem_t) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) = deBruijn_inc 0 inc t := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_subst, deBruijn_inc]
    | hdb m =>
      intro ts inc
      simp [deBruijn_subst, deBruijn_inc, show ¬ m + (inc + ts.length) < ts.length by omega]
      omega
    | happ ts' tn ih =>
      intro ts inc
      simp only [deBruijn_subst, deBruijn_inc, List.map_map, sem_t.Tapp.injEq, and_true]
      exact List.map_congr_left (fun t ht => ih t ht ts inc)
  refine ⟨h1, ?_⟩
  intro ts' ts inc
  simp only [List.map_map]
  exact List.map_congr_left (fun t _ => h1 t ts inc)
/- HOL4: [local]
Theorem type_e_subst_lem7:
  (!t sk targs targs' tvs' tvs''.
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
     (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
 (!ts sk targs targs' tvs' tvs''.
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
       (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts))))
-/
theorem type_e_subst_lem7 :
    (∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' tvs'' : List tvarN),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
        (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))) t)) ∧
    (∀ (ts : List sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' tvs'' : List tvarN),
      (ts.map (deBruijn_subst 0 targs)).map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
      (ts.map (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))))).map
        (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have h1 : ∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
        (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))) t) := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_subst]
    | hdb m =>
      intro sk targs targs'
      by_cases c1 : m < targs.length
      · simp [deBruijn_subst, c1, show m < targs.length + sk by omega]
        rw [EL_map' _ _ _ c1]
      by_cases c2 : m < targs.length + sk
      · simp [deBruijn_subst, c1, c2, show m - targs.length < sk by omega]
      by_cases c3 : m < targs'.length + (targs.length + sk)
      · have hj : m - (targs.length + sk) < targs'.length := by omega
        simp [deBruijn_subst, c1, c2, c3, show ¬ m - targs.length < sk by omega,
          show m - targs.length < targs'.length + sk by omega]
        rw [show m - targs.length - sk = m - (targs.length + sk) by omega, EL_map' _ _ _ hj,
          EL_map' _ _ _ hj]
        have := (subst_inc_cancel.1 (EL (m - (targs.length + sk)) targs')
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) sk)
        simp only [List.length_map] at this
        rw [show sk + targs.length = targs.length + sk by omega] at this
        exact this.symm
      · simp [deBruijn_subst, c1, c2, c3, show ¬ m - targs.length < sk by omega,
          show ¬ m - targs.length < targs'.length + sk by omega,
          show ¬ m - targs'.length < targs.length by omega]
        omega
    | happ ts tn ih =>
      intro sk targs targs'
      simp only [deBruijn_subst, List.map_map, sem_t.Tapp.injEq, and_true]
      exact List.map_congr_left (fun t ht => ih t ht sk targs targs')
  refine ⟨fun t sk targs targs' _ _ => h1 t sk targs targs', ?_⟩
  intro ts sk targs targs' _ _
  simp only [List.map_map]
  exact List.map_congr_left (fun t _ => h1 t sk targs targs')
/- HOL4:
Theorem deBruijn_subst_id:
 (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts))
-/
theorem deBruijn_subst_id :
    (∀ (t : sem_t) (n : Nat),
      check_freevars n [] t →
      deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n) t = t) ∧
    (∀ (ts : List sem_t) (n : Nat),
      EVERY (check_freevars n []) ts →
      ts.map (deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n)) = ts) := by
  have h1 : ∀ (t : sem_t) (n : Nat),
      check_freevars n [] t →
      deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n) t = t := by
    intro t
    induction t using sem_t.ind' with
    | hv => simp [deBruijn_subst]
    | hdb m =>
      intro n h
      simp at h
      simp [deBruijn_subst, GENLIST, h, EL]
    | happ ts tn ih =>
      intro n h
      simp only [check_freevars_Tapp, List.all_eq_true] at h
      simp only [deBruijn_subst, sem_t.Tapp.injEq, and_true]
      exact list_map_eq_self (fun t ht => ih t ht n (h t ht))
  refine ⟨h1, ?_⟩
  intro ts n h
  simp only [EVERY, List.all_eq_true] at h
  exact list_map_eq_self (fun t ht => h1 t n (h t ht))
/- HOL4:
Theorem deBruijn_subst_freevars:
 !skip targs t tvs.
  skip = 0 ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t
  ⇒
  check_freevars tvs [] (deBruijn_subst skip targs t)
-/
theorem deBruijn_subst_freevars :
    ∀ (skip : Nat) (targs : List sem_t) (t : sem_t) (tvs : Nat),
      skip = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t →
      check_freevars tvs [] (deBruijn_subst skip targs t) := by
  intro skip targs t tvs ⟨hs, hts, hc⟩
  subst hs
  exact deBruijn_subst_check_freevars2 tvs [] t targs 0 [] ⟨hc, hts⟩
/- HOL4:
Theorem tenv_abbrev_ok_lookup:
 !tenvT tn tvs t.
  tenv_abbrev_ok tenvT ∧
  nsLookup tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t
-/
theorem tenv_abbrev_ok_lookup :
    ∀ (tenvT : tenv_abbrev) (tn : cml_id modN typeN) (tvs : List tvarN) (t : sem_t),
      tenv_abbrev_ok tenvT ∧
      nsLookup tenvT tn = some (tvs, t) →
      check_freevars 0 tvs t := by
  intro tenvT tn tvs t ⟨h1, h2⟩
  exact h1 _ _ h2
theorem ast_t.ind' {P : ast_t → Prop}
    (hv : ∀ tv, P (.Atvar tv)) (hf : ∀ t1 t2, P t1 → P t2 → P (.Atfun t1 t2))
    (ht : ∀ ts, (∀ t ∈ ts, P t) → P (.Attup ts))
    (ha : ∀ ts tn, (∀ t ∈ ts, P t) → P (.Atapp ts tn)) : ∀ t, P t
  | .Atvar tv => hv tv
  | .Atfun t1 t2 => hf t1 t2 (ast_t.ind' hv hf ht ha t1) (ast_t.ind' hv hf ht ha t2)
  | .Attup ts => ht ts (fun t _ => ast_t.ind' hv hf ht ha t)
  | .Atapp ts tn => ha ts tn (fun t _ => ast_t.ind' hv hf ht ha t)

/- HOL4:
Theorem check_freevars_type_name_subst:
 !tvs t dbmax tenvT.
  tenv_abbrev_ok tenvT ∧
  check_type_names tenvT t ∧
  check_freevars_ast tvs t
  ⇒
  check_freevars dbmax tvs (type_name_subst tenvT t)
-/
theorem check_freevars_type_name_subst :
    ∀ (tvs : List tvarN) (t : ast_t) (dbmax : Nat) (tenvT : tenv_abbrev),
      tenv_abbrev_ok tenvT ∧
      check_type_names tenvT t ∧
      check_freevars_ast tvs t →
      check_freevars dbmax tvs (type_name_subst tenvT t) := by
  intro tvs t dbmax tenvT ⟨hok, hn, hf⟩
  induction t using ast_t.ind' with
  | hv tv => simpa [type_name_subst, check_freevars_ast] using hf
  | hf t1 t2 ih1 ih2 =>
    simp only [check_type_names, Bool.and_eq_true, check_freevars_ast] at hn hf
    simp [type_name_subst, Tfn, ih1 hn.1 hf.1, ih2 hn.2 hf.2]
  | ht ts ih =>
    simp only [check_type_names_Attup, check_freevars_ast_Attup, List.all_eq_true] at hn hf
    simp only [type_name_subst, Ttup, check_freevars_Tapp, List.all_map, List.all_eq_true,
      Function.comp]
    intro t ht; exact ih t ht (hn t ht) (hf t ht)
  | ha ts tn ih =>
    simp only [check_type_names_Atapp, check_freevars_ast_Atapp, List.all_eq_true,
      Bool.and_eq_true] at hn hf
    obtain ⟨hl, hn⟩ := hn
    simp only [type_name_subst]
    cases hlk : nsLookup tenvT tn with
    | none =>
      simp only [Ttup, check_freevars_Tapp, List.all_map, List.all_eq_true, Function.comp]
      intro t ht; exact ih t ht (hn t ht) (hf t ht)
    | some p =>
      obtain ⟨tvs', t'⟩ := p
      simp only [hlk, beq_iff_eq] at hl
      have hc := tenv_abbrev_ok_lookup tenvT tn tvs' t' ⟨hok, hlk⟩
      apply check_freevars_subst_single dbmax tvs' t' tvs (ts.map (type_name_subst tenvT))
      refine ⟨by simpa using hl, check_freevars_add _ _ _ hc _ (Nat.zero_le _), ?_⟩
      simp only [EVERY, List.all_map, List.all_eq_true, Function.comp]
      intro t ht; exact ih t ht (hn t ht) (hf t ht)
/- HOL4:
Theorem tenv_ctor_ok_merge[simp]:
   !tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2)
-/
theorem tenv_ctor_ok_merge :
    ∀ (tenvC1 tenvC2 : tenv_ctor),
      tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2 →
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) := by
  intro tenvC1 tenvC2 ⟨h1, h2⟩
  exact nsAll_nsAppend _ _ _ ⟨h1, h2⟩
/- HOL4:
Theorem tenv_ctor_ok_lookup:
   !tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
    ⇒
    EVERY (check_freevars 0 tvs) ts
-/
theorem tenv_ctor_ok_lookup :
    ∀ (tenvC : tenv_ctor) (cn : cml_id modN conN) (tvs : List tvarN) (ts : List sem_t) (tn : type_ident),
      tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = some (tvs, ts, tn) →
      EVERY (check_freevars 0 tvs) ts := by
  intro tenvC cn tvs ts tn ⟨h1, h2⟩
  exact h1 _ _ h2
/- HOL4:
Theorem bind_tvar_rewrites[simp]:
   (!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs e. num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs n t e. num_tvs (Bind_name n tvs t e) = num_tvs e) ∧
   (!tvs e. num_tvs Empty = 0) ∧
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc+tvs) e) ∧
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) ⇔ tenv_val_exp_ok e) ∧
   (!targs tvs e.
     deBruijn_subst_tenvE targs (bind_tvar tvs e) =
     bind_tvar tvs (deBruijn_subst_tenvE targs e))
-/
theorem bind_tvar_rewrites :
    (∀ (tvs : Nat) (e1 e2 : tenv_val_exp),
      db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      num_tvs (.Bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (n : mlstring) (tvs : Nat) (t : sem_t) (e : tenv_val_exp),
      num_tvs (.Bind_name n tvs t e) = num_tvs e) ∧
    (num_tvs .Empty = 0) ∧
    (∀ (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp),
      tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e) ∧
    (∀ (targs : List sem_t) (tvs : Nat) (e : tenv_val_exp),
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
      bind_tvar tvs (deBruijn_subst_tenvE targs e)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tvs e1 e2; by_cases h : tvs = 0 <;> simp [bind_tvar, db_merge, h]
  · intro tvs e; by_cases h : tvs = 0 <;> simp [bind_tvar, num_tvs, h]
  · intro tvs e; simp [num_tvs]
  · intro n tvs t e; simp [num_tvs]
  · simp [num_tvs]
  · intro n inc tvs e; by_cases h : tvs = 0 <;> simp [bind_tvar, tveLookup, h]
  · intro tvs e; by_cases h : tvs = 0 <;> simp [bind_tvar, tenv_val_exp_ok, h]
  · intro targs tvs e; by_cases h : tvs = 0 <;> simp [bind_tvar, deBruijn_subst_tenvE, h]
/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x
-/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  intro x; simp [bind_tvar]
/- HOL4:
Theorem tveLookup_subst_none:
 !n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE
-/
theorem tveLookup_subst_none :
    ∀ (targs : List sem_t) (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
      tveLookup n inc e = none := by
  intro targs n inc e
  induction e generalizing inc with
  | Empty => simp [deBruijn_subst_tenvE, tveLookup]
  | Bind_tvar tvs e ih => simp [deBruijn_subst_tenvE, tveLookup, ih]
  | Bind_name x tvs t e ih =>
    simp only [deBruijn_subst_tenvE, tveLookup]
    split <;> simp_all
/- HOL4:
Theorem tveLookup_db_merge_none:
 !n inc e1 e2.
  tveLookup n inc (db_merge e1 e2) = NONE
  ⇔
  tveLookup n inc e1 = NONE ∧ tveLookup n (num_tvs e1 + inc) e2 = NONE
-/
theorem tveLookup_db_merge_none :
    ∀ (n : mlstring) (inc : Nat) (e1 e2 : tenv_val_exp),
      tveLookup n inc (db_merge e1 e2) = none ↔
      tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none := by
  intro n inc e1 e2
  induction e1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar tvs e ih =>
    simp only [db_merge, tveLookup, num_tvs, ih]
    rw [show num_tvs e + (inc + tvs) = tvs + num_tvs e + inc by omega]
  | Bind_name x tvs t e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    split <;> simp_all
/- HOL4:
Theorem tveLookup_inc_none:
 !n inc e.
  tveLookup n inc e = NONE
  ⇔
  tveLookup n 0 e = NONE
-/
theorem tveLookup_inc_none :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc e = none ↔
      tveLookup n 0 e = none := by
  intro n inc e
  induction e generalizing inc with
  | Empty => simp [tveLookup]
  | Bind_tvar tvs e ih => simp only [tveLookup]; rw [ih, ih (0 + tvs)]
  | Bind_name x tvs t e ih =>
    simp only [tveLookup]
    split <;> simp_all
theorem deBruijn_inc_id_of_check (skip n : Nat) (l : List tvarN) (t : sem_t)
    (h : check_freevars skip l t) : deBruijn_inc skip n t = t := by
  induction t using sem_t.ind' with
  | hv => simp [deBruijn_inc]
  | hdb m => simp at h; simp [deBruijn_inc, h]
  | happ ts tn ih =>
    simp only [check_freevars_Tapp, List.all_eq_true] at h
    simp only [deBruijn_inc, sem_t.Tapp.injEq, and_true]
    exact list_map_eq_self (fun t ht => ih t ht (h t ht))

/- HOL4:
Theorem tveLookup_freevars:
   !n tvs tenvE tvs' t.
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    tveLookup n tvs tenvE = SOME (tvs',t)
    ⇒
    check_freevars tvs' [] t
-/
theorem tveLookup_freevars_thm :
    ∀ (n : mlstring) (tvs : Nat) (tenvE : tenv_val_exp) (tvs' : Nat) (t : sem_t),
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      tveLookup n tvs tenvE = some (tvs', t) →
      check_freevars tvs' [] t := by
  intro n tvs tenvE
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro tvs' t ⟨hok, hn, hl⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hn hl
    exact ih (tvs + k) tvs' t ⟨hok, by omega, hl⟩
  | Bind_name x k t' e ih =>
    intro tvs' t ⟨hok, hn, hl⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hn hl
    split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [hn, Nat.add_zero] at hok
      rw [deBruijn_inc_id_of_check _ _ _ _ hok.1]; exact hok.1
    · exact ih tvs tvs' t ⟨hok.2, hn, hl⟩
/- HOL4: [local]
Theorem tveLookup_freevars:
  !e n inc t tvs.
  tenv_val_exp_ok e ∧
  tveLookup n inc e = SOME (tvs, t)
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t
-/
theorem tveLookup_freevars_local :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : sem_t) (tvs : Nat),
      tenv_val_exp_ok e ∧
      tveLookup n inc e = some (tvs, t) →
      check_freevars (tvs + inc + num_tvs e) [] t := by
  intro e n
  induction e with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro inc t tvs ⟨hok, hl⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hl
    have := ih (inc + k) t tvs ⟨hok, hl⟩
    simp only [num_tvs]
    rwa [show tvs + inc + (k + num_tvs e) = tvs + (inc + k) + num_tvs e by omega]
  | Bind_name x k t' e ih =>
    intro inc t tvs ⟨hok, hl⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hl
    split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have := check_freevars_deBruijn_inc _ _ _ hok.1 inc k
      simp only [num_tvs]
      rwa [show inc + (k + num_tvs e) = k + inc + num_tvs e by omega] at this
    · exact ih inc t tvs ⟨hok.2, hl⟩
/- HOL4:
Theorem bind_var_list_append:
 !n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3)
-/
theorem bind_var_list_append :
    ∀ (n : Nat) (te1 te2 : List (mlstring × sem_t)) (te3 : tenv_val_exp),
      bind_var_list n (te1 ++ te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) := by
  intro n te1 te2 te3
  induction te1 with
  | nil => rfl
  | cons p te1 ih => obtain ⟨x, t⟩ := p; simp [bind_var_list, ih]
/- HOL4:
Theorem num_tvs_bind_var_list[simp]:
 !tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE
-/
theorem num_tvs_bind_var_list :
    ∀ (tvs : Nat) (env : List (mlstring × sem_t)) (tenvE : tenv_val_exp),
      num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE := by
  intro tvs env tenvE
  induction env with
  | nil => rfl
  | cons p env ih => obtain ⟨x, t⟩ := p; simp [bind_var_list, num_tvs, ih]
/- HOL4:
Theorem tenv_val_exp_ok_bvl:
 !tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE)
-/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (mlstring × sem_t)),
      tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd) →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  intro tenvE env ⟨hok, hc⟩
  simp only [EVERY, List.all_eq_true, List.mem_map] at hc
  induction env with
  | nil => exact hok
  | cons p env ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, tenv_val_exp_ok, num_tvs_bind_var_list, Nat.zero_add]
    refine ⟨hc t ⟨(x, t), by simp, rfl⟩, ih (fun a ⟨b, hb, hb'⟩ => hc a ⟨b, by simp [hb], hb'⟩)⟩
/- HOL4:
Theorem tveLookup_subst_some:
   ∀n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t)
    ⇒
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t)
-/
theorem tveLookup_subst_some :
    ∀ (n : mlstring) (e : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (t : sem_t) (inc : Nat),
      tveLookup n inc e = some (tvs, t) →
      tveLookup n inc (deBruijn_subst_tenvE targs e) =
        some (tvs, deBruijn_subst (tvs + inc + num_tvs e)
          (targs.map (deBruijn_inc 0 (tvs + inc + num_tvs e))) t) := by
  intro n e targs
  induction e with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro tvs t inc hl
    simp only [tveLookup, deBruijn_subst_tenvE, num_tvs] at hl ⊢
    rw [ih tvs t (inc + k) hl]
    rw [show tvs + (inc + k) + num_tvs e = tvs + inc + (k + num_tvs e) by omega]
  | Bind_name x k t' e ih =>
    intro tvs t inc hl
    simp only [tveLookup, deBruijn_subst_tenvE, num_tvs] at hl ⊢
    split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp only [↓reduceIte, *]
      have := type_e_subst_lem5.1 t' k inc (num_tvs e) targs
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      exact this
    · simp only [*]
      exact ih tvs t inc hl
/- HOL4:
Theorem num_tvs_db_merge[simp]:
 !e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2
-/
theorem num_tvs_db_merge :
    ∀ (e1 e2 : tenv_val_exp),
      num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 := by
  intro e1 e2
  induction e1 with
  | Empty => simp [db_merge, num_tvs]
  | Bind_tvar k e ih => simp [db_merge, num_tvs, ih]; omega
  | Bind_name x k t e ih => simp [db_merge, num_tvs, ih]
/- HOL4:
Theorem num_tvs_deBruijn_subst_tenvE[simp]:
 !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE
-/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List sem_t) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by
  intro targs tenvE
  induction tenvE with
  | Empty => rfl
  | Bind_tvar k e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
  | Bind_name x k t e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
/- HOL4:
Theorem tveLookup_inc_some:
 !n inc e tvs t inc2.
   tveLookup n inc e = SOME (tvs, t)
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t'))
-/
theorem tveLookup_inc_some :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp) (tvs : Nat) (t : sem_t) (inc2 : Nat),
      tveLookup n inc e = some (tvs, t) →
      ∃ (t' : sem_t),
        t = deBruijn_inc tvs inc t' ∧
        tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t') := by
  intro n inc e
  induction e generalizing inc with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro tvs t inc2 hl
    simp only [tveLookup] at hl ⊢
    obtain ⟨t', h1, h2⟩ := ih (inc + k) tvs t (inc2 + k) hl
    refine ⟨deBruijn_inc tvs k t', ?_, ?_⟩
    · rw [h1, deBruijn_inc_deBruijn_inc]
    · rw [h2, deBruijn_inc_deBruijn_inc]
  | Bind_name x k t' e ih =>
    intro tvs t inc2 hl
    simp only [tveLookup] at hl ⊢
    split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨t', rfl, by simp [*]⟩
    · simp only [*]
      exact ih inc tvs t inc2 hl
/- HOL4:
Theorem tveLookup_freevars_subst:
   !tenvE targs n t inc.
    EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
    tveLookup n inc tenvE = SOME (LENGTH targs,t) ∧
    tenv_val_exp_ok tenvE
    ⇒
    check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)
-/
theorem tveLookup_freevars_subst :
    ∀ (tenvE : tenv_val_exp) (targs : List sem_t) (n : mlstring) (t : sem_t) (inc : Nat),
      EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
      tveLookup n inc tenvE = some (targs.length, t) ∧
      tenv_val_exp_ok tenvE →
      check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := by
  intro tenvE targs n t inc ⟨hts, hl, hok⟩
  have h := tveLookup_freevars_local tenvE n inc t targs.length ⟨hok, hl⟩
  have := check_freevars_subst _ [] t h (inc + num_tvs tenvE) targs 0
    ⟨by omega, by simpa using hts⟩
  simpa using this
/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2
-/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp),
      tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by
  intro e1 e2
  induction e1 with
  | Empty => simp [db_merge]
  | Bind_tvar k e ih => intro h; exact ih h
  | Bind_name x k t e ih => intro h; exact ih h.2
/- HOL4:
Theorem tveLookup_no_tvs:
 !tvs l tenv n t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0
  ⇒
  (tveLookup n tvs tenv = SOME (l,t)
   ⇔
   tveLookup n 0 tenv = SOME (l,t))
-/
theorem tveLookup_no_tvs :
    ∀ (tvs : Nat) (l : Nat) (tenv : tenv_val_exp) (n : mlstring) (t : sem_t),
      tenv_val_exp_ok tenv ∧
      num_tvs tenv = 0 →
      (tveLookup n tvs tenv = some (l, t) ↔
       tveLookup n 0 tenv = some (l, t)) := by
  intro tvs l tenv n t
  induction tenv generalizing tvs with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro ⟨hok, hn⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hn ⊢
    rw [ih (tvs + k) ⟨hok, by omega⟩, ih (0 + k) ⟨hok, by omega⟩]
  | Bind_name x k t' e ih =>
    intro ⟨hok, hn⟩
    simp only [tenv_val_exp_ok, num_tvs, tveLookup] at hok hn ⊢
    split
    · rw [hn, Nat.add_zero] at hok
      rw [deBruijn_inc_id_of_check _ _ _ _ hok.1, deBruijn_inc_id_of_check _ _ _ _ hok.1]
    · exact ih tvs ⟨hok.2, hn⟩
/- HOL4:
Theorem deBruijn_subst_E_bvl:
 !tenv1 tenv2 tvs.
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
  =
  bind_var_list tvs
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
          (deBruijn_subst_tenvE targs tenv2)
-/
theorem deBruijn_subst_E_bvl :
    ∀ (targs : List sem_t) (tenv1 : List (mlstring × sem_t)) (tenv2 : tenv_val_exp) (tvs : Nat),
      deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) =
      bind_var_list tvs
        (tenv1.map (fun (x, t) => (x, deBruijn_subst (tvs + num_tvs tenv2)
          (targs.map (deBruijn_inc 0 (tvs + num_tvs tenv2))) t)))
        (deBruijn_subst_tenvE targs tenv2) := by
  intro targs tenv1 tenv2 tvs
  induction tenv1 with
  | nil => rfl
  | cons p tenv1 ih =>
    obtain ⟨x, t⟩ := p
    simp [bind_var_list, deBruijn_subst_tenvE, ih, num_tvs_bind_var_list]
/- HOL4:
Theorem db_merge_bvl:
 !tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3)
-/
theorem db_merge_bvl :
    ∀ (tenv1 : List (mlstring × sem_t)) (tenv2 tenv3 : tenv_val_exp) (tvs : Nat),
      db_merge (bind_var_list tvs tenv1 tenv2) tenv3 =
      bind_var_list tvs tenv1 (db_merge tenv2 tenv3) := by
  intro tenv1 tenv2 tenv3 tvs
  induction tenv1 with
  | nil => rfl
  | cons p tenv1 ih =>
    obtain ⟨x, t⟩ := p
    simp [bind_var_list, db_merge, ih]
/- HOL4:
Theorem tveLookup_db_merge_some:
   !n inc tenvE1 tenvE2 tvs t.
    tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t)
    ⇔
    tveLookup n inc tenvE1 = SOME (tvs,t) ∨
    (tveLookup n inc tenvE1 = NONE ∧
     tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs, t))
-/
theorem tveLookup_db_merge_some :
    ∀ (n : mlstring) (inc : Nat) (tenvE1 tenvE2 : tenv_val_exp) (tvs : Nat) (t : sem_t),
      tveLookup n inc (db_merge tenvE1 tenvE2) = some (tvs, t) ↔
      tveLookup n inc tenvE1 = some (tvs, t) ∨
      (tveLookup n inc tenvE1 = none ∧
       tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t)) := by
  intro n inc tenvE1 tenvE2 tvs t
  induction tenvE1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar k e ih =>
    simp only [db_merge, tveLookup, num_tvs, ih]
    rw [show num_tvs e + (inc + k) = k + num_tvs e + inc by omega]
  | Bind_name x k t' e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    split
    · simp
    · exact ih inc
/- HOL4: Theorem type_op_cases:
   Computed by HOL4 from type_op_def (SIMP_CONV with type_op_def, the case_eq
   theorems, DNF_ss, and PULL_EXISTS). Written here as that case expansion. -/
theorem type_op_cases_thm :
    ∀ (op_ : op) (ts : List sem_t) (t3 : sem_t),
      type_op op_ ts t3 ↔
        (∃ u1 u2, op_ = .Opapp ∧ ts = [u1, u2] ∧ u1 = Tfn u2 t3) ∨
        (∃ sh n u1, op_ = .Shift .W8 sh n ∧ ts = [u1] ∧ u1 = Tword8 ∧ t3 = Tword8) ∨
        (∃ sh n u1, op_ = .Shift .W64 sh n ∧ ts = [u1] ∧ u1 = Tword64 ∧ t3 = Tword64) ∨
        (∃ u1 u2, op_ = .Equality ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool) ∨
        (∃ a ty, op_ = .Arith a ty ∧ (∀ arg, arg ∈ ts → arg = t_of ty) ∧ t3 = t_of ty ∧
          supported_arith a ty = some ts.length) ∨
        (∃ ty1 ty2 u1, op_ = .FromTo ty1 ty2 ∧ ts = [u1] ∧ u1 = t_of ty1 ∧ t3 = t_of ty2 ∧
          supported_conversion ty1 ty2 = true) ∨
        (∃ tst ty u1 u2, op_ = .Test tst ty ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool ∧
          u1 = t_of ty ∧ supported_test tst ty = true) ∨
        (∃ u1 u2, op_ = .Opassign ∧ ts = [u1, u2] ∧ u1 = Tref u2 ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Opref ∧ ts = [u1] ∧ t3 = Tref u1) ∨
        (∃ u1, op_ = .Opderef ∧ ts = [u1] ∧ u1 = Tref t3) ∨
        (∃ u1 u2, op_ = .Aw8alloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tword8 ∧ t3 = Tword8array) ∨
        (∃ u1 u2, op_ = .Aw8sub ∧ ts = [u1, u2] ∧ u1 = Tword8array ∧ u2 = Tint ∧ t3 = Tword8) ∨
        (∃ u1, op_ = .Aw8length ∧ ts = [u1] ∧ u1 = Tword8array ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aw8update ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tword8 ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyStrStr ∧ ts = [u1, u2, u3] ∧ u1 = Tstring ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyStrAw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tstring ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyAw8Str ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyAw8Aw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tword8array ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Implode ∧ ts = [u1] ∧ u1 = Tlist Tchar ∧ t3 = Tstring) ∨
        (∃ u1, op_ = .Explode ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tlist Tchar) ∨
        (∃ u1 u2, op_ = .Strsub ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tint ∧ t3 = Tchar) ∨
        (∃ u1, op_ = .Strlen ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tint) ∨
        (∃ u1, op_ = .Strcat ∧ ts = [u1] ∧ u1 = Tlist Tstring ∧ t3 = Tstring) ∨
        (∃ u1 ctor, op_ = .VfromList ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tlist_num ∧
          t3 = Tvector u1) ∨
        (∃ u1 u2, op_ = .Vsub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tvector t3 = u1) ∨
        (∃ u1 ctor, op_ = .Vlength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tvector_num ∧ t3 = Tint) ∨
        (∃ u1 u2, op_ = .Aalloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ t3 = Tarray u2) ∨
        (∃ u1, op_ = .AallocEmpty ∧ ts = [u1] ∧ u1 = Ttup [] ∧ ∃ u2, t3 = Tarray u2) ∨
        (∃ u1 u2, op_ = .Asub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tarray t3 = u1) ∨
        (∃ u1 ctor, op_ = .Alength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tarray_num ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aupdate ∧ ts = [u1, u2, u3] ∧ u1 = Tarray u3 ∧ u2 = Tint ∧
          t3 = Ttup []) ∨
        (∃ u1 u2, op_ = .ConfigGC ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tint ∧ t3 = Ttup []) ∨
        (∃ nm u1 u2, op_ = .FFI nm ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tword8array ∧
          t3 = Ttup []) ∨
        (∃ u1 ctor u2, op_ = .ListAppend ∧ ts = [.Tapp [u1] ctor, u2] ∧ ctor = Tlist_num ∧
          u2 = sem_t.Tapp [u1] ctor ∧ t3 = u2) := by
  intro op_ ts t3
  constructor
  · intro h
    unfold type_op at h
    split at h <;> simp_all [and_assoc] <;> first | exact h.1 | exact h.1 ▸ h.2.2.1
  · simp only [or_imp, forall_exists_index, and_imp]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros; subst_vars; simp_all [type_op]) <;> first | assumption | exact ⟨_, rfl⟩
theorem type_ps_length_aux : ∀ {tvs : Nat} {tenvC : type_env} {ps : List pat} {ts : List sem_t}
    {tenv : List (varN × sem_t)}, type_ps tvs tenvC ps ts tenv → ps.length = ts.length
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ h2 => by simp [type_ps_length_aux h2]

mutual
theorem type_p_freevars_aux : ∀ {tvs : Nat} {tenvC : type_env} {p : pat} {t : sem_t}
    {env' : List (varN × sem_t)}, type_p tvs tenvC p t env' →
    check_freevars tvs [] t ∧ ∀ x ∈ env', check_freevars tvs [] x.2
  | _, _, _, _, _, .pany _ _ _ h => ⟨h, by simp⟩
  | _, _, _, _, _, .pvar _ _ _ _ h => ⟨h, by simp [h]⟩
  | _, _, _, _, _, .plit_int _ _ _ => ⟨by simp [Tint], by simp⟩
  | _, _, _, _, _, .plit_char _ _ _ => ⟨by simp [Tchar], by simp⟩
  | _, _, _, _, _, .plit_str _ _ _ => ⟨by simp [Tstring], by simp⟩
  | _, _, _, _, _, .plit_word8 _ _ _ => ⟨by simp [Tword8], by simp⟩
  | _, _, _, _, _, .plit_word64 _ _ _ => ⟨by simp [Tword64], by simp⟩
  | _, _, _, _, _, .pcon_some _ _ _ _ _ _ _ _ _ h1 _ h3 _ =>
    ⟨by simpa using h1, (type_ps_freevars_aux h3).2⟩
  | _, _, _, _, _, .pcon_none _ _ _ _ _ h =>
    ⟨by simpa [Ttup] using (type_ps_freevars_aux h).1, (type_ps_freevars_aux h).2⟩
  | _, _, _, _, _, .pref _ _ _ _ _ h =>
    ⟨by simpa [Tref] using (type_p_freevars_aux h).1, (type_p_freevars_aux h).2⟩
  | _, _, _, _, _, .pas _ _ _ _ _ _ h => by
    have := type_p_freevars_aux h
    refine ⟨this.1, ?_⟩
    intro x hx; simp at hx; rcases hx with hx | rfl
    · exact this.2 x hx
    · exact this.1
  | _, _, _, _, _, .ptannot _ _ _ _ _ _ _ h => type_p_freevars_aux h
theorem type_ps_freevars_aux : ∀ {tvs : Nat} {tenvC : type_env} {ps : List pat} {ts : List sem_t}
    {env' : List (varN × sem_t)}, type_ps tvs tenvC ps ts env' →
    (∀ t ∈ ts, check_freevars tvs [] t) ∧ ∀ x ∈ env', check_freevars tvs [] x.2
  | _, _, _, _, _, .nil _ _ => ⟨by simp, by simp⟩
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ h1 h2 => by
    have a := type_p_freevars_aux h1
    have b := type_ps_freevars_aux h2
    refine ⟨?_, ?_⟩
    · intro t ht; simp at ht; rcases ht with rfl | ht
      · exact a.1
      · exact b.1 t ht
    · intro x hx; simp at hx; rcases hx with hx | hx
      · exact b.2 _ hx
      · exact a.2 _ hx
end

theorem tenv_val_exp_ok_bvl_gen (tvs : Nat) (bindings : List (mlstring × sem_t))
    (tenv' : tenv_val_exp) (hok : tenv_val_exp_ok tenv')
    (hb : ∀ x ∈ bindings, check_freevars (tvs + num_tvs tenv') [] x.2) :
    tenv_val_exp_ok (bind_var_list tvs bindings tenv') := by
  induction bindings with
  | nil => exact hok
  | cons p bindings ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, tenv_val_exp_ok, num_tvs_bind_var_list]
    exact ⟨hb (x, t) (by simp), ih (fun y hy => hb y (by simp [hy]))⟩

mutual
theorem type_p_tenvV_aux : ∀ {tvs : Nat} {tenv : type_env} {p : pat} {t : sem_t}
    {b : List (varN × sem_t)} (tenvV : tenv_val), type_p tvs tenv p t b →
    type_p tvs { tenv with v := tenvV } p t b
  | _, _, _, _, _, _, .pany _ _ _ h => .pany _ _ _ h
  | _, _, _, _, _, _, .pvar _ _ _ _ h => .pvar _ _ _ _ h
  | _, _, _, _, _, _, .plit_int _ _ _ => .plit_int _ _ _
  | _, _, _, _, _, _, .plit_char _ _ _ => .plit_char _ _ _
  | _, _, _, _, _, _, .plit_str _ _ _ => .plit_str _ _ _
  | _, _, _, _, _, _, .plit_word8 _ _ _ => .plit_word8 _ _ _
  | _, _, _, _, _, _, .plit_word64 _ _ _ => .plit_word64 _ _ _
  | _, _, _, _, _, V, .pcon_some _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    .pcon_some _ _ _ _ _ _ _ _ _ h1 h2 (type_ps_tenvV_aux V h3) h4
  | _, _, _, _, _, V, .pcon_none _ _ _ _ _ h => .pcon_none _ _ _ _ _ (type_ps_tenvV_aux V h)
  | _, _, _, _, _, V, .pref _ _ _ _ _ h => .pref _ _ _ _ _ (type_p_tenvV_aux V h)
  | _, _, _, _, _, V, .pas _ _ _ _ _ _ h => .pas _ _ _ _ _ _ (type_p_tenvV_aux V h)
  | _, _, _, _, _, V, .ptannot _ _ _ _ _ h1 h2 h => .ptannot _ _ _ _ _ h1 h2 (type_p_tenvV_aux V h)
theorem type_ps_tenvV_aux : ∀ {tvs : Nat} {tenv : type_env} {ps : List pat} {ts : List sem_t}
    {b : List (varN × sem_t)} (tenvV : tenv_val), type_ps tvs tenv ps ts b →
    type_ps tvs { tenv with v := tenvV } ps ts b
  | _, _, _, _, _, _, .nil _ _ => .nil _ _
  | _, _, _, _, _, V, .cons _ _ _ _ _ _ _ _ h1 h2 =>
    .cons _ _ _ _ _ _ _ _ (type_p_tenvV_aux V h1) (type_ps_tenvV_aux V h2)
end

theorem type_es_list_rel_aux : ∀ {tenv : type_env} {tenvE : tenv_val_exp} {es : List exp}
    {ts : List sem_t}, type_es tenv tenvE es ts → LIST_REL (type_e tenv tenvE) es ts
  | _, _, _, _, .nil _ _ => .nil
  | _, _, _, _, .cons _ _ _ _ _ _ h1 h2 => .cons _ _ _ _ h1 (type_es_list_rel_aux h2)

theorem type_funs_freevars_aux : ∀ {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {env : List (varN × sem_t)},
    type_funs tenv tenvE funs env → ∀ x ∈ env, check_freevars (num_tvs tenvE) [] x.2
  | _, _, _, _, .nil _ _ => by simp
  | _, _, _, _, .cons _ _ _ _ _ _ _ _ _ h1 _ h3 _ => by
    intro x hx; simp at hx; rcases hx with rfl | hx
    · exact h1
    · exact type_funs_freevars_aux h3 x hx

/- HOL4:
Theorem type_ps_length:
 ∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)
-/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (tenv : List (varN × sem_t)),
      type_ps tvs tenvC ps ts tenv → ps.length = ts.length := fun _ _ _ _ _ h => type_ps_length_aux h
/- HOL4:
Theorem type_p_freevars:
 (!tvs tenvC p t env'.
   type_p tvs tenvC p t env' ⇒
   check_freevars tvs [] t ∧
   EVERY (check_freevars tvs []) (MAP SND env')) ∧
 (!tvs tenvC ps ts env'.
   type_ps tvs tenvC ps ts env' ⇒
   EVERY (check_freevars tvs []) ts ∧
   EVERY (check_freevars tvs []) (MAP SND env'))
-/
theorem type_p_freevars :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : sem_t) (env' : List (varN × sem_t)),
      type_p tvs tenvC p t env' →
      check_freevars tvs [] t ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (env' : List (varN × sem_t)),
      type_ps tvs tenvC ps ts env' →
      EVERY (check_freevars tvs []) ts ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) := by
  refine ⟨fun _ _ _ _ _ h => ?_, fun _ _ _ _ _ h => ?_⟩
  · have := type_p_freevars_aux h
    refine ⟨this.1, ?_⟩
    simp only [EVERY, List.all_eq_true, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩; exact this.2 x hx
  · have := type_ps_freevars_aux h
    simp only [EVERY, List.all_eq_true, List.mem_map]
    refine ⟨this.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩; exact this.2 x hx
/- HOL4:
Theorem type_p_subst:
 (!n tenv p t new_bindings. type_p n tenv p t new_bindings ⇒
    !targs' inc tvs targs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenv
           p
           (deBruijn_subst inc targs' t)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings)) ∧
 (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings ⇒
    !targs' inc targs tvs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_ps (inc +  tvs) tenv
           ps
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings))
-/
theorem type_p_subst :
    (∀ (n : Nat) (tenv : type_env) (p : pat) (t : sem_t) (new_bindings : List (varN × sem_t)),
      type_p n tenv p t new_bindings →
      ∀ (targs' : List sem_t) (inc : Nat) (tvs : Nat) (targs : List sem_t),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc) →
        type_p (inc + tvs) tenv p
          (deBruijn_subst inc targs' t)
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) ∧
    (∀ (n : Nat) (tenv : type_env) (ps : List pat) (ts : List sem_t) (new_bindings : List (varN × sem_t)),
      type_ps n tenv ps ts new_bindings →
      ∀ (targs' : List sem_t) (inc : Nat) (targs : List sem_t) (tvs : Nat),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc) →
        type_ps (inc + tvs) tenv ps
          (ts.map (deBruijn_subst inc targs'))
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := by
  have hp : ∀ (n : Nat) (tenv : type_env) (p : pat) (t : sem_t) (new_bindings : List (varN × sem_t)),
      type_p n tenv p t new_bindings →
      ∀ (inc : Nat) (tvs : Nat) (targs : List sem_t),
        tenv_abbrev_ok tenv.t ∧ tenv_ctor_ok tenv.c ∧ n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs →
        type_p (inc + tvs) tenv p
          (deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t)
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t))) := by
    intro n tenv p t nb h inc tvs targs hh
    obtain ⟨hab, hct, hn, hev⟩ := hh
    refine type_p.rec
      (motive_1 := fun p t nb _ => type_p (inc + tvs) tenv p
          (deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t)
          (nb.map (fun (x, t) => (x, deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t))))
      (motive_2 := fun ps ts nb _ => type_ps (inc + tvs) tenv ps
          (ts.map (deBruijn_subst inc (targs.map (deBruijn_inc 0 inc))))
          (nb.map (fun (x, t) => (x, deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t))))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro t hc
      exact .pany _ _ _ (check_freevars_lem _ _ _ hc targs inc tvs ⟨hn, hev⟩)
    · intro x t hc
      exact .pvar _ _ _ _ (check_freevars_lem _ _ _ hc targs inc tvs ⟨hn, hev⟩)
    · intro _; simpa [Tint, deBruijn_subst] using type_p.plit_int _ _ _
    · intro _; simpa [Tchar, deBruijn_subst] using type_p.plit_char _ _ _
    · intro _; simpa [Tstring, deBruijn_subst] using type_p.plit_str _ _ _
    · intro _; simpa [Tword8, deBruijn_subst] using type_p.plit_word8 _ _ _
    · intro _; simpa [Tword64, deBruijn_subst] using type_p.plit_word64 _ _ _
    · intro cn ps ts' tvs' ts tn bindings h1 h2 _ h4 ih
      have hok := tenv_ctor_ok_lookup _ _ _ _ _ ⟨hct, h4⟩
      have heq := type_subst_deBruijn_subst_list (.Tvar_db 0) tvs' tvs' ts'
        (targs.map (deBruijn_inc 0 inc)) ts inc ⟨h2.symm, hok⟩
      simp only [ZIP] at heq
      rw [heq] at ih
      simp only [deBruijn_subst]
      refine .pcon_some _ _ _ _ _ _ _ _ _ ?_ (by simpa using h2) ih h4
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact check_freevars_lem _ _ _ (h1 t0 ht0) targs inc tvs ⟨hn, hev⟩
    · intro ps ts bindings _ ih
      simpa [Ttup, deBruijn_subst] using type_p.pcon_none _ _ _ _ _ ih
    · intro p t bindings _ ih
      simpa [Tref, deBruijn_subst] using type_p.pref _ _ _ _ _ ih
    · intro p t bindings v_ _ ih
      simpa using type_p.pas _ _ _ _ _ v_ ih
    · intro p t bindings h1 h2 _ ih
      have hnil := nil_deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) (type_name_subst tenv.t t)
        (check_freevars_type_name_subst [] t inc tenv.t ⟨hab, h2, h1⟩)
      rw [hnil] at ih ⊢
      exact .ptannot _ _ _ _ _ h1 h2 ih
    · exact .nil _ _
    · intro p t bindings ps ts bindings' _ _ ih1 ih2
      simpa using type_ps.cons _ _ _ _ _ _ _ _ ih1 ih2
  refine ⟨fun n tenv p t nb h targs' inc tvs targs hh => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, rfl⟩ := hh
    exact hp n tenv p t nb h inc tvs targs ⟨h1, h2, h3, h4⟩
  · intro n tenv ps
    induction ps with
    | nil => intro ts nb h targs' inc targs tvs _; cases h; exact .nil _ _
    | cons p ps ih =>
      intro ts nb h targs' inc targs tvs hh
      cases h with
      | cons _ t b _ ts' b' h1 h2 =>
        obtain ⟨ha, hb, hc, hd, rfl⟩ := hh
        simpa using type_ps.cons _ _ _ _ _ _ _ _ (hp _ _ _ _ _ h1 inc tvs targs ⟨ha, hb, hc, hd⟩)
          (ih _ _ h2 _ inc targs tvs ⟨ha, hb, hc, hd, rfl⟩)
/- HOL4:
Theorem type_p_bvl:
   (!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv'))
-/
theorem type_p_bvl :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : sem_t) (bindings : List (varN × sem_t)),
      type_p tvs tenvC p t bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (bindings : List (varN × sem_t)),
      type_ps tvs tenvC ps ts bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := by
  refine ⟨fun _ _ _ _ _ h tenv' hok => ?_, fun _ _ _ _ _ h tenv' hok => ?_⟩
  · exact tenv_val_exp_ok_bvl_gen _ _ _ hok (fun x hx =>
      check_freevars_add _ _ _ ((type_p_freevars_aux h).2 x hx) _ (Nat.le_add_right _ _))
  · exact tenv_val_exp_ok_bvl_gen _ _ _ hok (fun x hx =>
      check_freevars_add _ _ _ ((type_ps_freevars_aux h).2 x hx) _ (Nat.le_add_right _ _))
/- HOL4:
Theorem type_p_tenvV_indep:
 (!p tvs tenv t bindings tenvV.
  type_p tvs tenv p t bindings = type_p tvs (tenv with v := tenvV) p t bindings) ∧
 (!ps tvs tenv t bindings tenvV.
  type_ps tvs tenv ps t bindings = type_ps tvs (tenv with v := tenvV) ps t bindings)
-/
theorem type_p_tenvV_indep :
    (∀ (p : pat) (tvs : Nat) (tenv : type_env) (t : sem_t) (bindings : List (varN × sem_t)) (tenvV : tenv_val),
      type_p tvs tenv p t bindings = type_p tvs { tenv with v := tenvV } p t bindings) ∧
    (∀ (ps : List pat) (tvs : Nat) (tenv : type_env) (t : List sem_t) (bindings : List (varN × sem_t)) (tenvV : tenv_val),
      type_ps tvs tenv ps t bindings = type_ps tvs { tenv with v := tenvV } ps t bindings) := by
  refine ⟨fun p tvs tenv t b V => propext ⟨type_p_tenvV_aux V, fun h => ?_⟩,
    fun ps tvs tenv t b V => propext ⟨type_ps_tenvV_aux V, fun h => ?_⟩⟩
  · exact type_p_tenvV_aux (tenv := { tenv with v := V }) tenv.v h
  · exact type_ps_tenvV_aux (tenv := { tenv with v := V }) tenv.v h
/- HOL4:
Theorem type_es_list_rel:
 !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts
-/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List sem_t) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts := by
  intro es ts tenv tenvE
  apply propext
  refine ⟨type_es_list_rel_aux, fun h => ?_⟩
  induction h with
  | nil => exact .nil _ _
  | cons x y xs ys h1 _ ih => exact .cons _ _ _ _ _ _ h1 ih
/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts)
-/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts → es.length = ts.length := by
  intro tenv tenvE es ts h
  have := type_es_list_rel_aux h
  clear h
  induction this with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simp [ih]
/- HOL4:
Theorem tenv_val_exp_ok_bvl_funs:
   !funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list 0 env tenvE)
-/
theorem tenv_val_exp_ok_bvl_funs :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × sem_t))
      (tenv : type_env) (bindings : List (varN × sem_t))
      (tenv_val_ : tenv_val) (tenvE : tenv_val_exp),
      type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
      tenv_val_exp_ok tenvE →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  intro funs env tenv bindings _ tenvE ⟨h, hok⟩
  have := type_funs_freevars_aux h
  rw [num_tvs_bind_var_list] at this
  exact tenv_val_exp_ok_bvl_gen _ _ _ hok (fun x hx => by simpa using this x hx)
theorem type_e_freevars_rec (tenv : type_env) :
    ∀ {tenvE : tenv_val_exp} {e : exp} {t : sem_t},
    type_e tenv tenvE e t → tenv_val_exp_ok tenvE → tenv_val_ok tenv.v →
    check_freevars (num_tvs tenvE) [] t := by
  intro tenvE e t h
  refine type_e.rec
    (motive_1 := fun tenvE _ t _ => tenv_val_exp_ok tenvE → tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t)
    (motive_2 := fun tenvE _ ts _ => tenv_val_exp_ok tenvE → tenv_val_ok tenv.v →
      ∀ t ∈ ts, check_freevars (num_tvs tenvE) [] t)
    (motive_3 := fun tenvE _ env _ => ∀ x ∈ env, check_freevars (num_tvs tenvE) [] x.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; simp [Tint]
  · intros; simp [Tchar]
  · intros; simp [Tstring]
  · intros; simp [Tword8]
  · intros; simp [Tword64]
  · intros; simp [Tdouble]
  · intro _ _ _ h1 _ _ _ _; exact h1
  · intro _ _ _ _ _ _ _ _ _ _ ih _ hok hv; exact ih hok hv
  · intro _ _ _ _ _ _ _ h1 _ _ _ _ _ _; simpa using h1
  · intro _ _ _ _ ih hok hv; simpa [Ttup] using ih hok hv
  · intro tenvE n tvs t targs h1 h2 h3 hok hv
    simp only [lookup_var] at h3
    have hts : EVERY (check_freevars (0 + num_tvs tenvE) []) targs = true := by
      simpa [EVERY] using h2
    cases hx : lookup_varE n tenvE with
    | some p =>
      rw [hx] at h3; cases h3
      simp only [lookup_varE] at hx
      split at hx
      · have := tveLookup_freevars_local tenvE _ 0 t tvs ⟨hok, hx⟩
        simpa using check_freevars_subst _ [] t this (num_tvs tenvE) targs 0
          ⟨by omega, hts⟩
      · cases hx
    | none =>
      rw [hx] at h3
      have := hv _ _ h3
      simp only at this
      have := check_freevars_add _ _ _ this (tvs + num_tvs tenvE) (Nat.le_add_right _ _)
      simpa using check_freevars_subst _ [] t this (num_tvs tenvE) targs 0
        ⟨by omega, hts⟩
  · intro tenvE n e t1 t2 h1 _ ih hok hv
    have := ih ⟨by simpa using h1, hok⟩ hv
    simp only [num_tvs] at this
    simp [Tfn, h1, this]
  · intro _ _ _ _ _ _ _ h3 _ _ _; exact h3
  · intros; simp [Tbool]
  · intro _ _ _ _ _ _ _ _ _ ih _ hok hv; exact ih hok hv
  · intro tenvE e t1 t2 pes bindings_of _ hne _ hp _ _ ih hok hv
    obtain ⟨pe, hpe⟩ := List.exists_mem_of_ne_nil pes hne
    have hok' : tenv_val_exp_ok (bind_var_list 0 (bindings_of pe) tenvE) :=
      tenv_val_exp_ok_bvl_gen _ _ _ hok (fun x hx => by
        simpa using (type_p_freevars_aux (hp pe hpe)).2 x hx)
    have := ih pe hpe hok' hv
    rwa [num_tvs_bind_var_list] at this
  · intro tenvE n e1 t1 e2 t2 _ _ ih1 ih2 hok hv
    have c1 := ih1 hok hv
    have hok2 : tenv_val_exp_ok (opt_bind_name n 0 t1 tenvE) := by
      cases n with
      | none => exact hok
      | some n => exact ⟨by simpa using c1, hok⟩
    have := ih2 hok2 hv
    cases n <;> simpa [opt_bind_name, num_tvs] using this
  · intro tenvE funs bindings e t _ _ ihf ih hok hv
    have hok' : tenv_val_exp_ok (bind_var_list 0 bindings tenvE) :=
      tenv_val_exp_ok_bvl_gen _ _ _ hok (fun x hx => by
        simpa [num_tvs_bind_var_list] using ihf x hx)
    have := ih hok' hv
    rwa [num_tvs_bind_var_list] at this
  · intro _ _ _ _ _ _ ih hok hv; exact ih hok hv
  · intro _ _ _ _ _ ih hok hv; exact ih hok hv
  · intros; simp
  · intro _ _ _ _ _ _ _ ih1 ih2 hok hv x hx
    simp at hx; rcases hx with rfl | hx
    · exact ih1 hok hv
    · exact ih2 hok hv x hx
  · intros; simp
  · intro _ _ _ _ _ _ _ _ h1 _ _ _ _ ih x hx
    simp at hx; rcases hx with rfl | hx
    · exact h1
    · exact ih x hx

/- HOL4:
Theorem type_e_freevars:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env))
-/
theorem type_e_freevars :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × sem_t)),
      type_funs tenv tenvE funs env →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := by
  refine ⟨fun tenv _ _ _ h ⟨hok, hv⟩ => type_e_freevars_rec tenv h hok hv,
    fun _ _ _ _ h ⟨hok, hv⟩ => ?_, fun _ _ _ _ h _ => ?_⟩
  · have hl := type_es_list_rel_aux h
    simp only [EVERY, List.all_eq_true]
    clear h
    induction hl with
    | nil => simp
    | cons x y xs ys h1 _ ih =>
      intro t ht; simp at ht
      rcases ht with rfl | ht
      · exact type_e_freevars_rec _ h1 hok hv
      · exact ih t ht
  · simp only [EVERY, List.all_eq_true, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩; exact type_funs_freevars_aux h x hx
theorem tveLookup_bind_tvar (x : mlstring) (i a : Nat) (E : tenv_val_exp) :
    tveLookup x i (bind_tvar a E) = tveLookup x (i + a) E := by
  unfold bind_tvar
  split
  · rename_i h; simp at h; subst h; rfl
  · rfl

theorem tveLookup_closed (x : mlstring) :
    ∀ (E : tenv_val_exp) (inc tvs : Nat) (t : sem_t), tenv_val_exp_ok E → num_tvs E = 0 →
      tveLookup x inc E = some (tvs, t) → check_freevars tvs [] t
  | .Empty, _, _, _, _, _, h => by simp [tveLookup] at h
  | .Bind_tvar a E, inc, tvs, t, hok, h0, h => by
    simp only [num_tvs] at h0
    simp only [tveLookup] at h
    exact tveLookup_closed x E _ tvs t hok (by omega) h
  | .Bind_name y a t0 E, inc, tvs, t, hok, h0, h => by
    simp only [num_tvs] at h0
    simp only [tenv_val_exp_ok, h0, Nat.add_zero] at hok
    simp only [tveLookup] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [deBruijn_inc_id_of_check _ _ _ _ hok.1]; exact hok.1
    · exact tveLookup_closed x E inc tvs t hok.2 h0 h

theorem type_e_subst_var (tenv : type_env) (E1 E2 : tenv_val_exp) (targs : List sem_t) (tvs : Nat)
    (n : cml_id modN varN) (tvs' : Nat) (t : sem_t) (targs0 : List sem_t)
    (h2 : num_tvs E2 = 0) (hv : tenv_val_ok tenv.v)
    (hok : tenv_val_exp_ok (db_merge E1 (bind_tvar targs.length E2)))
    (hev : EVERY (check_freevars tvs []) targs) (hl : tvs' = targs0.length)
    (hc : ∀ ta ∈ targs0, check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length E2))) [] ta)
    (hlk : lookup_var n (db_merge E1 (bind_tvar targs.length E2)) tenv = some (tvs', t)) :
    type_e tenv (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) (.Var n)
      (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1)))
        (deBruijn_subst 0 targs0 t)) := by
  have hbt : ∀ a, num_tvs (bind_tvar a E2) = a := by
    intro a; unfold bind_tvar; split
    · rename_i h; simp at h; simp [h, h2]
    · simp [num_tvs, h2]
  have hE2ok : tenv_val_exp_ok E2 := by
    have := tenv_val_exp_ok_db_merge _ _ hok
    unfold bind_tvar at this; split at this
    · exact this
    · exact this
  rw [(type_e_subst_lem7).1 t (num_tvs E1) targs0 targs [] []]
  refine type_e.var _ _ _ targs0.length _ _ (by simp) ?_ ?_
  · intro ta hta
    simp only [List.mem_map] at hta
    obtain ⟨ta0, h0, rfl⟩ := hta
    have := hc ta0 h0
    rw [num_tvs_db_merge, hbt] at this
    rw [num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, hbt]
    exact type_e_subst_lem3 _ _ _ this tvs targs (num_tvs E1) ⟨rfl, hev⟩
  · subst hl
    -- closed-type helper
    have hnil : ∀ t, check_freevars targs0.length [] t →
        deBruijn_subst (targs0.length + num_tvs E1)
          (targs.map (deBruijn_inc 0 (targs0.length + num_tvs E1))) t = t := by
      intro t ht
      exact nil_deBruijn_subst _ _ _ (check_freevars_add _ _ _ ht _ (by omega))
    unfold lookup_var at hlk ⊢
    cases hE : lookup_varE n (db_merge E1 (bind_tvar targs.length E2)) with
    | none =>
      rw [hE] at hlk
      have hnone : lookup_varE n (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) = none := by
        cases n with
        | Short x =>
          simp only [lookup_varE] at hE ⊢
          rw [tveLookup_db_merge_none] at hE ⊢
          obtain ⟨h1, h2'⟩ := hE
          refine ⟨(tveLookup_subst_none _ _ _ _).2 h1, ?_⟩
          rw [tveLookup_bind_tvar] at h2' ⊢
          exact (tveLookup_inc_none _ _ _).2 ((tveLookup_inc_none _ _ _).1 h2')
        | Long _ _ => rfl
      rw [hnone]
      simp only at hlk ⊢
      rw [hlk]
      have := nsLookup_nsAll _ _ _ _ ⟨hv, hlk⟩
      simp only at this
      rw [hnil t this]
    | some p =>
      rw [hE] at hlk
      simp only [Option.some.injEq] at hlk
      subst hlk
      cases n with
      | Long _ _ => simp [lookup_varE] at hE
      | Short x =>
        simp only [lookup_varE] at hE ⊢
        rcases (tveLookup_db_merge_some _ _ _ _ _ _).1 hE with h | ⟨hn, h⟩
        · have := tveLookup_subst_some _ _ targs _ _ _ h
          rw [(tveLookup_db_merge_some _ _ _ _ _ _).2 (Or.inl (by simpa using this))]
        · rw [tveLookup_bind_tvar, tveLookup_no_tvs _ _ _ _ _ ⟨hE2ok, h2⟩] at h
          have hcl := tveLookup_closed x E2 0 _ _ hE2ok h2 h
          rw [hnil t hcl]
          rw [(tveLookup_db_merge_some _ _ _ _ _ _).2 (Or.inr ⟨(tveLookup_subst_none _ _ _ _).2 hn, ?_⟩)]
          rw [tveLookup_bind_tvar, tveLookup_no_tvs _ _ _ _ _ ⟨hE2ok, h2⟩]
          exact h

theorem ALOOKUP_map_snd_none {α β : Type} [BEq α] (f : β → β) :
    ∀ (l : List (α × β)) (k : α), ALOOKUP l k = none →
      ALOOKUP (l.map (fun (x, t) => (x, f t))) k = none
  | [], _, _ => rfl
  | (a, b) :: l, k, h => by
    simp only [ALOOKUP] at h
    simp only [List.map, ALOOKUP]
    split at h
    · cases h
    · rename_i hne; simp only [hne]; exact ALOOKUP_map_snd_none f l k h

theorem deBruijn_subst_t_of (k : Nat) (s : List sem_t) (ty : prim_type) :
    deBruijn_subst k s (t_of ty) = t_of ty := by
  rcases ty with _ | _ | _ | _ | ⟨_ | _⟩ | _ <;>
    simp [t_of, deBruijn_subst, Tbool, Tint, Tchar, Tstring, Tword8, Tword64, Tdouble]

theorem type_op_deBruijn_subst (o_ : op) (ts : List sem_t) (t : sem_t) (k : Nat) (s : List sem_t)
    (h : type_op o_ ts t) : type_op o_ (ts.map (deBruijn_subst k s)) (deBruijn_subst k s t) := by
  unfold type_op at h
  split at h <;> simp_all [type_op, deBruijn_subst, deBruijn_subst_t_of, Tfn, Tword8, Tword64, Tbool,
    Tref, Ttup, Tint, Tword8array, Tstring, Tlist, Tchar, Tvector, Tarray]
  all_goals first
   | (intro a ha; rw [h.1 a ha, deBruijn_subst_t_of])
   | (obtain ⟨rfl, _, rfl, _⟩ := h; exact deBruijn_subst_t_of _ _ _)
   | (obtain ⟨_, rfl⟩ := h; simp [deBruijn_subst])
   | (obtain ⟨_, t2, rfl⟩ := h; exact ⟨deBruijn_subst k s t2, by simp [deBruijn_subst]⟩)

/- HOL4:
Theorem type_e_subst:
 (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧ ...
  (three-part mutual induction on type_e / type_es / type_funs)
  with free variable tenvE2
-/
theorem type_e_subst :
    ∀ (tenvE2 : tenv_val_exp),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          e (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          es (ts.map (deBruijn_subst (num_tvs tenvE1) targs'))) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × sem_t)),
      type_funs tenv tenvE funs env →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          funs (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1) targs' t)))) := by
  intro E2
  have hground : ∀ k s n, deBruijn_subst k s (.Tapp [] n) = .Tapp [] n := by
    intro k s n; simp [deBruijn_subst]
  have main : ∀ (tenv : type_env), num_tvs E2 = 0 → tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c →
      tenv_val_ok tenv.v → ∀ (tenvE : tenv_val_exp) (e : exp) (t : sem_t), type_e tenv tenvE e t →
      ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat),
        tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
        tenvE = db_merge E1 (bind_tvar targs.length E2) →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) e
          (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t) := by
    intro tenv h2 hab hct hv tenvE e t h
    have hbt : ∀ a, num_tvs (bind_tvar a E2) = a := by
      intro a; unfold bind_tvar; split
      · rename_i h; simp at h; simp [h, h2]
      · simp [num_tvs, h2]
    have hfv : ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (t : sem_t),
        EVERY (check_freevars tvs []) targs →
        check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length E2))) [] t →
        check_freevars (num_tvs (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2))) []
          (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t) := by
      intro E1 targs tvs t hev hc
      rw [num_tvs_db_merge, hbt] at hc
      rw [num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, hbt]
      exact type_e_subst_lem3 _ _ _ hc tvs targs (num_tvs E1) ⟨rfl, hev⟩
    have hbvl : ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (B : List (varN × sem_t)),
        db_merge (deBruijn_subst_tenvE targs (bind_var_list 0 B E1)) (bind_tvar tvs E2) =
        bind_var_list 0 (B.map (fun (x, t) =>
          (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
          (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) := by
      intro E1 targs tvs B
      rw [deBruijn_subst_E_bvl, db_merge_bvl]; simp
    have hpat : ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) p t0 B,
        EVERY (check_freevars tvs []) targs →
        type_p (num_tvs (db_merge E1 (bind_tvar targs.length E2))) tenv p t0 B →
        type_p (num_tvs (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2))) tenv p
          (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t0)
          (B.map (fun (x, t) =>
            (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t))) := by
      intro E1 targs tvs p t0 B hev hp
      rw [num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, hbt]
      exact type_p_subst.1 _ _ _ _ _ hp _ (num_tvs E1) tvs targs
        ⟨hab, hct, by rw [num_tvs_db_merge, hbt], hev, rfl⟩
    have hbranch : ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) p t0 B e t,
        tenv_val_exp_ok (db_merge E1 (bind_tvar targs.length E2)) →
        EVERY (check_freevars tvs []) targs →
        type_p (num_tvs (db_merge E1 (bind_tvar targs.length E2))) tenv p t0 B →
        (∀ (E1' : tenv_val_exp) (targs' : List sem_t) (tvs' : Nat),
          tenv_val_exp_ok (bind_var_list 0 B (db_merge E1 (bind_tvar targs.length E2))) →
          EVERY (check_freevars tvs' []) targs' →
          bind_var_list 0 B (db_merge E1 (bind_tvar targs.length E2)) =
            db_merge E1' (bind_tvar targs'.length E2) →
          type_e tenv (db_merge (deBruijn_subst_tenvE targs' E1') (bind_tvar tvs' E2)) e
            (deBruijn_subst (num_tvs E1') (targs'.map (deBruijn_inc 0 (num_tvs E1'))) t)) →
        type_e tenv (bind_var_list 0 (B.map (fun (x, t) =>
            (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
            (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2))) e
          (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t) := by
      intro E1 targs tvs p t0 B e t hok hev hp ih
      have hok' : tenv_val_exp_ok (bind_var_list 0 B (db_merge E1 (bind_tvar targs.length E2))) :=
        tenv_val_exp_ok_bvl _ _ ⟨hok, (type_p_freevars.1 _ _ _ _ _ hp).2⟩
      have := ih (bind_var_list 0 B E1) targs tvs hok' hev (db_merge_bvl _ _ _ _).symm
      rw [hbvl, num_tvs_bind_var_list] at this
      exact this
    refine type_e.rec
      (motive_1 := fun tenvE e t _ => ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat),
        tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
        tenvE = db_merge E1 (bind_tvar targs.length E2) →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) e
          (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t))
      (motive_2 := fun tenvE es ts _ => ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat),
        tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
        tenvE = db_merge E1 (bind_tvar targs.length E2) →
        type_es tenv (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) es
          (ts.map (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))))))
      (motive_3 := fun tenvE funs bindings _ => ∀ (E1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat),
        tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
        tenvE = db_merge E1 (bind_tvar targs.length E2) →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2)) funs
          (bindings.map (fun (x, t) =>
            (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t))))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro _ _ _ _ _ _ _ _; rw [Tint, hground]; exact .lit_int _ _ _
    · intro _ _ _ _ _ _ _ _; rw [Tchar, hground]; exact .lit_char _ _ _
    · intro _ _ _ _ _ _ _ _; rw [Tstring, hground]; exact .lit_str _ _ _
    · intro _ _ _ _ _ _ _ _; rw [Tword8, hground]; exact .lit_word8 _ _ _
    · intro _ _ _ _ _ _ _ _; rw [Tword64, hground]; exact .lit_word64 _ _ _
    · intro _ _ _ _ _ _ _ _; rw [Tdouble, hground]; exact .lit_float64 _ _ _
    · intro tenvE e t h1 _ ih E1 targs tvs hok hev heq
      subst heq
      have := ih E1 targs tvs hok hev rfl
      rw [Texn, hground] at this
      exact .raise _ _ _ _ (hfv _ _ _ _ hev h1) this
    · intro tenvE e t pes bindings_of _ hne hd hp _ ih1 ih2 E1 targs tvs hok hev heq
      subst heq
      refine .handle _ _ _ _ _ (fun pe => (bindings_of pe).map (fun (x, t) =>
          (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
        (ih1 E1 targs tvs hok hev rfl) hne hd ?_ ?_
      · intro pe hpe
        have := hpat E1 targs tvs _ _ _ hev (hp pe hpe)
        rw [Texn, hground] at this
        exact this
      · intro pe hpe
        exact hbranch E1 targs tvs _ _ _ _ _ hok hev (hp pe hpe) (ih2 pe hpe)
    · intro tenvE cn es ts' tvs' ts tn h1 h2' _ h4 ih E1 targs tvs hok hev heq
      subst heq
      have hok2 := tenv_ctor_ok_lookup _ _ _ _ _ ⟨hct, h4⟩
      have heq2 := type_subst_deBruijn_subst_list (.Tvar_db 0) tvs' tvs' ts'
        (targs.map (deBruijn_inc 0 (num_tvs E1))) ts (num_tvs E1) ⟨h2', hok2⟩
      simp only [ZIP] at heq2
      have := ih E1 targs tvs hok hev rfl
      rw [heq2] at this
      simp only [deBruijn_subst]
      refine .con_some _ _ _ _ _ _ _ _ ?_ (by simpa using h2') this h4
      intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact hfv _ _ _ _ hev (h1 t0 ht0)
    · intro tenvE es ts _ ih E1 targs tvs hok hev heq
      have := ih E1 targs tvs hok hev heq
      simp only [Ttup, deBruijn_subst]
      exact .con_none _ _ _ _ this
    · intro tenvE n tvs' t targs0 h1 h2' h3 E1 targs tvs hok hev heq
      subst heq
      exact type_e_subst_var tenv E1 E2 targs tvs n tvs' t targs0 h2 hv hok hev h1 h2' h3
    · intro tenvE n e t1 t2 h1 _ ih E1 targs tvs hok hev heq
      subst heq
      have := ih (.Bind_name n 0 t1 E1) targs tvs ⟨by simpa using h1, hok⟩ hev rfl
      simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at this
      simp only [Tfn, deBruijn_subst, List.map]
      exact .fun_ _ _ _ _ _ _ (hfv _ _ _ _ hev h1) this
    · intro tenvE o_ es ts t _ h2' h3 ih E1 targs tvs hok hev heq
      have hfv3 := hfv E1 targs tvs t hev (heq ▸ h3)
      exact .app _ _ _ _ _ _ (ih E1 targs tvs hok hev heq) (type_op_deBruijn_subst _ _ _ _ _ h2') hfv3
    · intro tenvE l e1 e2 _ _ ih1 ih2 E1 targs tvs hok hev heq
      have a := ih1 E1 targs tvs hok hev heq
      have b := ih2 E1 targs tvs hok hev heq
      rw [Tbool, hground] at a b ⊢
      exact .log _ _ _ _ _ a b
    · intro tenvE e1 e2 e3 t _ _ _ ih1 ih2 ih3 E1 targs tvs hok hev heq
      have a := ih1 E1 targs tvs hok hev heq
      rw [Tbool, hground] at a
      exact .if_ _ _ _ _ _ _ a (ih2 E1 targs tvs hok hev heq) (ih3 E1 targs tvs hok hev heq)
    · intro tenvE e t1 t2 pes bindings_of _ hne hd hp _ ih1 ih2 E1 targs tvs hok hev heq
      subst heq
      refine .mat _ _ _ _ _ _ (fun pe => (bindings_of pe).map (fun (x, t) =>
          (x, deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
        (ih1 E1 targs tvs hok hev rfl) hne hd ?_ ?_
      · intro pe hpe
        exact hpat E1 targs tvs _ _ _ hev (hp pe hpe)
      · intro pe hpe
        exact hbranch E1 targs tvs _ _ _ _ _ hok hev (hp pe hpe) (ih2 pe hpe)
    · intro tenvE n e1 t1 e2 t2 h1 _ ih1 ih2 E1 targs tvs hok hev heq
      subst heq
      have a := ih1 E1 targs tvs hok hev rfl
      cases n with
      | none =>
        exact .let_ _ _ _ _ _ _ _ a (ih2 E1 targs tvs hok hev rfl)
      | some x =>
        have hc1 := type_e_freevars.1 _ _ _ _ h1 ⟨hok, hv⟩
        have b := ih2 (.Bind_name x 0 t1 E1) targs tvs ⟨by simpa using hc1, hok⟩ hev rfl
        simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at b
        exact .let_ _ _ _ _ _ _ _ a b
    · intro tenvE funs bindings e t hf _ ih1 ih2 E1 targs tvs hok hev heq
      subst heq
      have hok' := tenv_val_exp_ok_bvl_funs _ _ _ _ tenv.v _ ⟨hf, hok⟩
      have a := ih1 (bind_var_list 0 bindings E1) targs tvs hok' hev (db_merge_bvl _ _ _ _).symm
      have b := ih2 (bind_var_list 0 bindings E1) targs tvs hok' hev (db_merge_bvl _ _ _ _).symm
      rw [hbvl, num_tvs_bind_var_list] at a b
      exact .letrec _ _ _ _ _ _ a b
    · intro tenvE e t h1 h2' _ ih E1 targs tvs hok hev heq
      have := ih E1 targs tvs hok hev heq
      have hnil := nil_deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1)))
        (type_name_subst tenv.t t)
        (check_freevars_type_name_subst [] t (num_tvs E1) tenv.t ⟨hab, h2', h1⟩)
      rw [hnil] at this ⊢
      exact .tannot _ _ _ _ h1 h2' this
    · intro tenvE e t l _ ih E1 targs tvs hok hev heq
      exact .lannot _ _ _ _ _ (ih E1 targs tvs hok hev heq)
    · intro _ _ _ _ _ _ _; exact .nil _ _
    · intro tenvE e t es ts _ _ ih1 ih2 E1 targs tvs hok hev heq
      exact .cons _ _ _ _ _ _ (ih1 E1 targs tvs hok hev heq) (ih2 E1 targs tvs hok hev heq)
    · intro _ _ _ _ _ _ _; exact .nil _ _
    · intro tenvE fn n e t1 t2 funs bindings h1 _ _ h4 ih1 ih2 E1 targs tvs hok hev heq
      subst heq
      have hc1 : check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length E2))) [] t1 := by
        simp only [Tfn, check_freevars_Tapp, List.all_cons, Bool.and_eq_true] at h1; exact h1.1
      have a := ih1 (.Bind_name n 0 t1 E1) targs tvs ⟨by simpa using hc1, hok⟩ hev rfl
      simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at a
      have hf := hfv _ _ _ _ hev h1
      simp only [Tfn, deBruijn_subst, List.map] at hf ⊢
      exact .cons _ _ _ _ _ _ _ _ _ hf a (ih2 E1 targs tvs hok hev rfl)
        (ALOOKUP_map_snd_none _ _ _ h4)
  refine ⟨?_, ?_, ?_⟩
  · intro tenv tenvE e t h E1 targs tvs targs' ⟨h2, hab, hct, hv, hok, hev, heq, ht⟩
    subst ht
    exact main tenv h2 hab hct hv tenvE e t h E1 targs tvs hok hev heq
  · intro tenv tenvE es
    induction es with
    | nil => intro ts h _ _ _ _ _; cases h; exact .nil _ _
    | cons e es ih =>
      intro ts h E1 targs tvs targs' hh
      cases h with
      | cons _ _ t _ ts h1 h2 =>
        obtain ⟨h2', hab, hct, hv, hok, hev, heq, ht⟩ := hh
        subst ht
        exact .cons _ _ _ _ _ _ (main tenv h2' hab hct hv _ _ _ h1 E1 targs tvs hok hev heq)
          (ih _ h2 E1 targs tvs _ ⟨h2', hab, hct, hv, hok, hev, heq, rfl⟩)
  · intro tenv tenvE funs
    induction funs with
    | nil => intro bindings h _ _ _ _ _; cases h; exact .nil _ _
    | cons f funs ih =>
      intro bindings h E1 targs tvs targs' hh
      cases h with
      | cons _ fn n e t1 t2 _ bindings h1 h2 h3 h4 =>
        obtain ⟨h2', hab, hct, hv, hok, hev, heq, ht⟩ := hh
        subst ht; subst heq
        have hbt : ∀ a, num_tvs (bind_tvar a E2) = a := by
          intro a; unfold bind_tvar; split
          · rename_i h; simp at h; simp [h, h2']
          · simp [num_tvs, h2']
        have hc1 : check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length E2))) [] t1 := by
          simp only [Tfn, check_freevars_Tapp, List.all_cons, Bool.and_eq_true] at h1; exact h1.1
        have a := main tenv h2' hab hct hv _ _ _ h2 (.Bind_name n 0 t1 E1) targs tvs
          ⟨by simpa using hc1, hok⟩ hev rfl
        simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at a
        have hf : check_freevars (num_tvs (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs E2))) []
            (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) (Tfn t1 t2)) := by
          rw [num_tvs_db_merge, hbt] at h1
          rw [num_tvs_db_merge, num_tvs_deBruijn_subst_tenvE, hbt]
          exact type_e_subst_lem3 _ _ _ h1 tvs targs (num_tvs E1) ⟨rfl, hev⟩
        simp only [Tfn, deBruijn_subst, List.map] at hf ⊢
        exact .cons _ _ _ _ _ _ _ _ _ hf a
          (ih _ h3 E1 targs tvs _ ⟨h2', hab, hct, hv, hok, hev, rfl, rfl⟩)
          (ALOOKUP_map_snd_none _ _ _ h4)
theorem type_funs_Tfn_aux : ∀ {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bindings : List (varN × sem_t)},
    type_funs tenv tenvE funs bindings → ∀ (n : varN) (t : sem_t),
    ALOOKUP bindings n = some t →
    ∃ (t1 t2 : sem_t), t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
  | _, _, _, _, .nil _ _ => by simp [ALOOKUP]
  | _, _, _, _, .cons _ _ _ _ _ _ _ _ _ h1 _ h3 _ => by
    intro n t hl
    simp only [ALOOKUP] at hl
    split at hl
    · simp at hl; subst hl; exact ⟨_, _, rfl, h1⟩
    · exact type_funs_Tfn_aux h3 n t hl

theorem type_funs_map_fst : ∀ {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bindings : List (varN × sem_t)},
    type_funs tenv tenvE funs bindings → funs.map Prod.fst = bindings.map Prod.fst
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ h3 _ => by simp [type_funs_map_fst h3]

theorem type_recfun_lookup_aux : ∀ {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bindings : List (varN × sem_t)},
    type_funs tenv tenvE funs bindings → ∀ (fn n : varN) (e : exp) (t1 t2 : sem_t),
    find_recfun fn funs = some (n, e) → ALOOKUP bindings fn = some (Tfn t1 t2) →
    type_e tenv (.Bind_name n 0 t1 tenvE) e t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
  | _, _, _, _, .nil _ _ => by simp [find_recfun]
  | _, _, _, _, .cons _ _ _ _ _ _ _ _ _ h1 h2 h3 _ => by
    intro fn n e t1 t2 hf hl
    simp only [find_recfun, ALOOKUP] at hf hl
    split at hf
    · rename_i hfn
      simp only [hfn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf hl
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Tfn, sem_t.Tapp.injEq, List.cons.injEq, and_true] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨h2, h1⟩
    · rename_i hfn
      simp only [hfn, Bool.false_eq_true, ↓reduceIte] at hl
      exact type_recfun_lookup_aux h3 fn n e t1 t2 hf hl

/- HOL4:
Theorem type_funs_Tfn:
   ∀tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings n = SOME t
    ⇒
    ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
-/
theorem type_funs_Tfn :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (tvs : Nat) (t : sem_t) (n : varN),
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings n = some t →
      ∃ (t1 t2 : sem_t), t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  intro tenv tenvE funs bindings _ t n ⟨h, hl⟩
  exact type_funs_Tfn_aux h n t hl
/- HOL4:
Theorem type_funs_lookup:
 ∀fn tenvE funs bindings n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃t. ALOOKUP bindings fn = SOME t)
-/
theorem type_funs_lookup :
    ∀ (fn : varN) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (n : varN) (e : exp) (tenv : type_env),
      (fn, n, e) ∈ funs ∧
      type_funs tenv tenvE funs bindings →
      ∃ (t : sem_t), ALOOKUP bindings fn = some t := by
  intro fn tenvE funs bindings n e tenv ⟨hm, h⟩
  have hfst := type_funs_map_fst h
  have : fn ∈ bindings.map Prod.fst := by
    rw [← hfst]; exact List.mem_map.2 ⟨_, hm, rfl⟩
  cases hx : ALOOKUP bindings fn with
  | some t => exact ⟨t, rfl⟩
  | none =>
    rw [ALOOKUP_none_iff] at hx
    exact absurd this hx
/- HOL4:
Theorem type_funs_find_recfun:
 ∀fn env funs bindings e tenv tenvE t.
  ALOOKUP bindings fn = SOME t ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))
-/
theorem type_funs_find_recfun :
    ∀ (fn : varN) (env : List (varN × sem_t)) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (e : exp) (tenv : type_env)
      (tenvE : tenv_val_exp) (t : sem_t),
      ALOOKUP bindings fn = some t ∧
      type_funs tenv tenvE funs bindings →
      ∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e) := by
  intro fn env funs bindings e tenv tenvE t ⟨hl, h⟩
  have hfst := type_funs_map_fst h
  have hm : fn ∈ funs.map Prod.fst := by
    rw [hfst]
    cases hx : ALOOKUP bindings fn with
    | some _ => exact List.mem_map.2 ⟨_, ALOOKUP_mem hx, rfl⟩
    | none => rw [hx] at hl; cases hl
  clear hl h hfst
  induction funs with
  | nil => simp at hm
  | cons f funs ih =>
    obtain ⟨f, x, e'⟩ := f
    simp only [find_recfun]
    split
    · exact ⟨_, _, rfl⟩
    · rename_i hne
      apply ih
      simp at hm
      rcases hm with rfl | hm
      · simp at hne
      · exact List.mem_map.2 (by obtain ⟨a, b, h⟩ := hm; exact ⟨(fn, a, b), h, rfl⟩)
/- HOL4:
Theorem type_recfun_lookup:
   ∀fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) ∧
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings fn = SOME (Tfn t1 t2)
    ⇒
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
-/
theorem type_recfun_lookup :
    ∀ (fn : varN) (funs : List (varN × varN × exp)) (n : varN) (e : exp)
      (tenv : type_env) (tenvE : tenv_val_exp) (bindings : List (varN × sem_t))
      (tvs : Nat) (t1 t2 : sem_t),
      find_recfun fn funs = some (n, e) ∧
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings fn = some (Tfn t1 t2) →
      type_e tenv (.Bind_name n 0 t1 tenvE) e t2 ∧
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  intro fn funs n e tenv tenvE bindings _ t1 t2 ⟨hf, h, hl⟩
  exact type_recfun_lookup_aux h fn n e t1 t2 hf hl
theorem type_funs_distinct_aux : ∀ {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bindings : List (varN × sem_t)},
    type_funs tenv tenvE funs bindings → ALL_DISTINCT (funs.map Prod.fst) = true
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ _ fn _ _ _ _ _ _ _ _ h3 hl => by
    simp only [List.map_cons, ALL_DISTINCT, type_funs_distinct_aux h3, Bool.and_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq]
    rw [type_funs_map_fst h3]
    rw [ALOOKUP_none_iff] at hl
    intro x hx e; subst e; exact hl hx

/- HOL4:
Theorem type_funs_distinct:
 ∀tenv tenvE funs bindings .
  type_funs tenv tenvE funs bindings
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs)
-/
theorem type_funs_distinct :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)),
      type_funs tenv tenvE funs bindings →
      ALL_DISTINCT (funs.map (fun (x, _, _) => x)) := by
  intro tenv tenvE funs bindings h
  have e : (funs.map (fun (x, _, _) => x)) = funs.map Prod.fst := by
    apply List.map_congr_left; intro p _; obtain ⟨a, b, c⟩ := p; rfl
  rw [e]
  exact type_funs_distinct_aux h
/- HOL4: [local]
Theorem type_e_subst_lem:
  ∀tenv tenvE e t targs tvs targs'.
  type_e tenv (Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t ∧
  num_tvs tenvE = 0 ∧ ...
  (with free variables x and t1)
-/
theorem type_e_subst_lem :
    ∀ (x : mlstring) (t1 : sem_t)
      (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t)
      (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
      type_e tenv (.Bind_name x 0 t1 (bind_tvar targs.length tenvE)) e t ∧
      num_tvs tenvE = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok (bind_tvar targs.length tenvE) ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t1 →
      type_e tenv (.Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE))
        e (deBruijn_subst 0 targs t) := by
  intro x t1 tenv tenvE e t targs tvs targs' ⟨h, h0, hab, hct, hv, hok, hev, hc⟩
  have hbt : num_tvs (bind_tvar targs.length tenvE) = targs.length := by
    unfold bind_tvar; split
    · rename_i h; simp at h; simp [h, h0]
    · simp [num_tvs, h0]
  have := (type_e_subst tenvE).1 tenv _ e t h (.Bind_name x 0 t1 .Empty) targs tvs
    (targs.map (deBruijn_inc 0 0))
    ⟨h0, hab, hct, hv, ⟨by simpa [hbt] using hc, hok⟩, hev, rfl, rfl⟩
  simpa [deBruijn_subst_tenvE, db_merge, num_tvs, deBruijn_inc0.2] using this
theorem type_def_to_ctMap_mem_gen (tenvT : tenv_abbrev) :
    ∀ (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (ids : List type_ident) (next : Nat) (stmp : stamp)
      (x : List tvarN × List sem_t × type_ident),
      (stmp, x) ∈ type_def_to_ctMap tenvT next tds ids →
      ∃ (i : Nat) (tvs : List tvarN) (tn : mlstring) (ctors : List (conN × List ast_t))
        (cn : conN) (cts : List ast_t),
        tds[i]? = some (tvs, tn, ctors) ∧ ids[i]? = some x.2.2 ∧ (cn, cts) ∈ ctors ∧
        stmp = .TypeStamp cn (next + i) ∧ x = (tvs, cts.map (type_name_subst tenvT), x.2.2)
  | [], ids, next, stmp, x, h => by cases ids <;> simp [type_def_to_ctMap] at h
  | (tvs, tn, ctors) :: tds, [], next, stmp, x, h => by simp [type_def_to_ctMap] at h
  | (tvs, tn, ctors) :: tds, id_ :: ids, next, stmp, x, h => by
    simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h
    rcases h with h | ⟨⟨cn, cts⟩, hm, he⟩
    · obtain ⟨i, tvs', tn', ctors', cn, cts, h1, h2, h3, h4, h5⟩ :=
        type_def_to_ctMap_mem_gen tenvT tds ids (next + 1) stmp x h
      refine ⟨i + 1, tvs', tn', ctors', cn, cts, by simpa using h1, by simpa using h2, h3, ?_, h5⟩
      rw [h4]; congr 1; omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨0, tvs, tn, ctors, cn, cts, by simp, by simp, hm, by simp, rfl⟩

theorem FUPDATE_LIST_some_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (m : Finmap α β) (k : α) (v : β),
      Finmap.FUPDATE_LIST m l k = some v → m k = some v ∨ (k, v) ∈ l
  | [], m, k, v, h => Or.inl h
  | (a, b) :: l, m, k, v, h => by
    simp only [Finmap.FUPDATE_LIST, List.foldl] at h
    rcases FUPDATE_LIST_some_mem l _ k v h with h | h
    · simp only [Finmap.FUPDATE] at h
      by_cases hk : k = a
      · subst hk; simp at h; subst h; simp
      · simp [hk] at h; exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem ALOOKUP_some_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), ALOOKUP l k = some v → (k, v) ∈ l
  | [], k, v, h => by simp [ALOOKUP] at h
  | (a, b) :: l, k, v, h => by
    simp only [ALOOKUP] at h
    by_cases hk : a = k
    · subst hk; simp at h; subst h; simp
    · simp [hk] at h; exact List.mem_cons_of_mem _ (ALOOKUP_some_mem l k v h)

theorem FUPDATE_FUNION_aux {α β : Type} [BEq α] :
    ∀ (l : List (α × β)) (n m : Finmap α β),
      Finmap.FUPDATE_LIST (Finmap.FUNION n m) l = Finmap.FUNION (Finmap.FUPDATE_LIST n l) m
  | [], n, m => rfl
  | kv :: l, n, m => by
    simp only [Finmap.FUPDATE_LIST, List.foldl]
    have : Finmap.FUPDATE (Finmap.FUNION n m) kv = Finmap.FUNION (Finmap.FUPDATE n kv) m := by
      funext x; simp only [Finmap.FUPDATE, Finmap.FUNION]; split <;> simp_all
    rw [this]; exact FUPDATE_FUNION_aux l _ m

/- HOL4:
Theorem mem_type_def_to_ctMap:
   !tenvT next tds ids stamp x.
    MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) ∧
    LENGTH tds = LENGTH ids
    ⇒
    ?cn i. stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds
-/
theorem mem_type_def_to_ctMap :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (ids : List type_ident) (stmp : stamp)
      (x : List tvarN × List sem_t × type_ident),
      (stmp, x) ∈ type_def_to_ctMap tenvT next tds ids ∧
      tds.length = ids.length →
      ∃ (cn : conN) (i : Nat), stmp = .TypeStamp cn i ∧ next ≤ i ∧ i < next + tds.length := by
  intro tenvT next tds ids stmp x ⟨h, hl⟩
  obtain ⟨i, tvs, tn, ctors, cn, cts, h1, h2, h3, h4, h5⟩ :=
    type_def_to_ctMap_mem_gen tenvT tds ids next stmp x h
  have : i < tds.length := by
    rcases Nat.lt_or_ge i tds.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at h1
  exact ⟨cn, next + i, h4, by omega, by omega⟩
/- HOL4:
Theorem ctMap_ok_merge_imp:
   !ctMap1 ctMap2.
    DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) ∧
    ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 ⇒
    ctMap_ok (FUNION ctMap1 ctMap2)
-/
theorem ctMap_ok_merge_imp :
    ∀ (ctMap1 ctMap2 : ctMap),
      Set.Disjoint
        (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap1))
        (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap2)) ∧
      ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 →
      ctMap_ok (Finmap.FUNION ctMap1 ctMap2) := by
  intro m1 m2 ⟨hd, h1, h2⟩
  have look : ∀ k v, Finmap.FUNION m1 m2 k = some v → m1 k = some v ∨ m2 k = some v := by
    intro k v h; simp only [Finmap.FUNION] at h; split at h
    · left; simp_all
    · right; exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v h; rcases look k v h with h | h
    · exact h1.1 k v h
    · exact h2.1 k v h
  · intro ex tvs ts ti h; rcases look _ _ h with h | h
    · exact h1.2.1 ex tvs ts ti h
    · exact h2.2.1 ex tvs ts ti h
  · intro cn x tvs ts ti h; rcases look _ _ h with h | h
    · exact h1.2.2.1 cn x tvs ts ti h
    · exact h2.2.2.1 cn x tvs ts ti h
  · intro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨ha, hb⟩
    rcases look _ _ ha with ha | ha <;> rcases look _ _ hb with hb | hb
    · exact h1.2.2.2 s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨ha, hb⟩
    · exact absurd ⟨⟨s1, by simp [Finmap.o_f, ha]⟩, ⟨s2, by simp [Finmap.o_f, hb]⟩⟩ (hd ti)
    · exact absurd ⟨⟨s2, by simp [Finmap.o_f, hb]⟩, ⟨s1, by simp [Finmap.o_f, ha]⟩⟩ (hd ti)
    · exact h2.2.2.2 s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨ha, hb⟩
/- HOL4:
Theorem ctMap_ok_lookup:
 !ctMap cn tvs ts ti tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = SOME (tvs,ts,ti))
  ⇒
  EVERY (check_freevars 0 tvs) ts
-/
theorem ctMap_ok_lookup :
    ∀ (ctMap_ : ctMap) (cn : conN) (tvs : List tvarN) (ts : List sem_t)
      (ti : type_ident) (tn : stamp),
      ctMap_ok ctMap_ ∧ Finmap.FLOOKUP ctMap_ tn = some (tvs, ts, ti) →
      EVERY (check_freevars 0 tvs) ts := by
  intro ctMap_ cn tvs ts ti tn ⟨h, hl⟩
  exact h.1 tn _ hl
/- HOL4:
Theorem type_def_to_ctMap_mem:
   !tenvT next tds tids.
    ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x ∧
    LENGTH tds = LENGTH tids
    ⇒
    MEM (SND (SND x)) tids
-/
theorem type_def_to_ctMap_mem :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tids : List type_ident) (k : stamp) (x : List tvarN × List sem_t × type_ident),
      ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = some x ∧
      tds.length = tids.length →
      x.2.2 ∈ tids := by
  intro tenvT next tds tids k x ⟨h, _⟩
  obtain ⟨i, tvs, tn, ctors, cn, cts, h1, h2, h3, h4, h5⟩ :=
    type_def_to_ctMap_mem_gen tenvT tds tids next k x (ALOOKUP_some_mem _ _ _ h)
  exact List.mem_of_getElem? h2
/- HOL4: [local]
Theorem fupdate2_union:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1)
-/
theorem fupdate2_union :
    ∀ (m : Finmap stamp (List tvarN × List sem_t × type_ident))
      (a1 a2 : List (stamp × (List tvarN × List sem_t × type_ident))),
      Finmap.FUPDATE_LIST (Finmap.FUPDATE_LIST m a1) a2 =
      Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY a2) (Finmap.FUPDATE_LIST m a1) := by
  intro m a1 a2
  have := FUPDATE_FUNION_aux a2 Finmap.FEMPTY (Finmap.FUPDATE_LIST m a1)
  rw [← this]; rfl
theorem ALL_DISTINCT_getElem?_inj {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (i j : Nat) (x : α), ALL_DISTINCT l = true →
      l[i]? = some x → l[j]? = some x → i = j
  | [], i, j, x, _, h, _ => by simp at h
  | y :: l, i, j, x, hd, hi, hj => by
    simp only [ALL_DISTINCT, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
      beq_iff_eq] at hd
    cases i <;> cases j
    · rfl
    · simp at hi hj; subst hi; exact absurd rfl (hd.1 _ (List.mem_of_getElem? hj))
    · simp at hi hj; subst hj; exact absurd rfl (hd.1 _ (List.mem_of_getElem? hi))
    · simp at hi hj; congr 1; exact ALL_DISTINCT_getElem?_inj l _ _ x hd.2 hi hj

theorem check_ctor_tenv_getElem? (tenvT : tenv_abbrev) :
    ∀ (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (i : Nat)
      tvs tn ctors (cn : conN) (cts : List ast_t),
      check_ctor_tenv tenvT tds = true → tds[i]? = some (tvs, tn, ctors) → (cn, cts) ∈ ctors →
      (∀ t ∈ cts, check_freevars_ast tvs t = true) ∧ (∀ t ∈ cts, check_type_names tenvT t = true)
  | [], i, _, _, _, _, _, _, h, _ => by simp at h
  | (tvs', tn', ctors') :: tds, i, tvs, tn, ctors, cn, cts, hc, hi, hm => by
    simp only [check_ctor_tenv, Bool.and_eq_true, List.all_eq_true] at hc
    cases i with
    | zero =>
      simp at hi; obtain ⟨rfl, rfl, rfl⟩ := hi
      have := hc.1.1.2 _ hm
      simp only [Bool.and_eq_true, List.all_eq_true] at this
      exact this
    | succ i => simp at hi; exact check_ctor_tenv_getElem? tenvT tds i tvs tn ctors cn cts hc.2 hi hm

/- HOL4:
Theorem ctMap_ok_type_defs:
   !tenvT next tds tids.
    ALL_DISTINCT tids ∧
    DISJOINT (set tids) (set prim_type_nums) ∧
    LENGTH tds = LENGTH tids ∧
    check_ctor_tenv tenvT tds ∧
    tenv_abbrev_ok tenvT
    ⇒
    ctMap_ok
      (FEMPTY |++
        REVERSE (type_def_to_ctMap tenvT next tds tids))
-/
theorem ctMap_ok_type_defs :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tids : List type_ident),
      ALL_DISTINCT tids ∧
      DISJOINT (fun x => x ∈ tids) (fun x => x ∈ prim_type_nums) ∧
      tds.length = tids.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      ctMap_ok (Finmap.FUPDATE_LIST Finmap.FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse) := by
  intro tenvT next tds tids ⟨hd, hdisj, hl, hc, hok⟩
  have mem : ∀ k v, Finmap.FUPDATE_LIST Finmap.FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse k = some v →
      ∃ (i : Nat) (tvs : List tvarN) (tn : mlstring) (ctors : List (conN × List ast_t))
        (cn : conN) (cts : List ast_t),
        tds[i]? = some (tvs, tn, ctors) ∧ tids[i]? = some v.2.2 ∧ (cn, cts) ∈ ctors ∧
        k = .TypeStamp cn (next + i) ∧ v = (tvs, cts.map (type_name_subst tenvT), v.2.2) := by
    intro k v h
    rcases FUPDATE_LIST_some_mem _ _ k v h with h | h
    · simp [Finmap.FEMPTY] at h
    · exact type_def_to_ctMap_mem_gen tenvT tds tids next k v (List.mem_reverse.mp h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k ⟨tvs0, ts0, ti0⟩ h
    obtain ⟨i, tvs, tn, ctors, cn, cts, h1, h2, h3, h4, h5⟩ := mem _ _ h
    simp only [Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl, -⟩ := h5
    have := check_ctor_tenv_getElem? tenvT tds i _ tn ctors cn cts hc h1 h3
    simp only [EVERY, List.all_eq_true, List.mem_map]
    rintro _ ⟨t, ht, rfl⟩
    exact check_freevars_type_name_subst _ t 0 tenvT ⟨hok, this.2 t ht, this.1 t ht⟩
  · intro ex tvs ts ti h
    obtain ⟨i, _, _, _, cn, _, _, _, _, h4, _⟩ := mem _ _ h
    cases h4
  · intro cn x tvs ts ti h hp
    obtain ⟨i, _, _, _, _, _, _, h2, _, _, _⟩ := mem _ _ h
    exact hdisj ti ⟨List.mem_of_getElem? h2, by simpa using hp⟩
  · intro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨ha, hb⟩
    obtain ⟨i, _, _, _, cn, _, _, h2, _, h4, _⟩ := mem _ _ ha
    obtain ⟨j, _, _, _, cn', _, _, h2', _, h4', _⟩ := mem _ _ hb
    have := ALL_DISTINCT_getElem?_inj tids i j ti hd h2 h2'
    subst this; subst h4; subst h4'
    simp [same_type]
/- HOL4:
Theorem nsLookup_add_tenvE1:
   !tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t ∧
    tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE1 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : mlstring) (tvs : Nat)
      (t : sem_t) (tvs2 : Nat),
      check_freevars tvs2 [] t ∧
      tveLookup n tvs tenvE = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  intro tenvE tenvV n tvs t tvs2
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro ⟨hc, hl⟩
    simp only [tveLookup] at hl
    exact ih (tvs + k) ⟨hc, hl⟩
  | Bind_name x k t' e ih =>
    intro ⟨hc, hl⟩
    simp only [tveLookup] at hl
    simp only [add_tenvE]
    split at hl
    · rename_i hx
      simp at hx; subst hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [nil_deBruijn_inc _ _ _ (Or.inr hc), nsLookup_nsBind.1]
    · rename_i hx
      rw [nsLookup_nsBind.2 _ _ _ _ (by simpa using fun h => hx (by simp [h]))]
      exact ih tvs ⟨hc, hl⟩
/- HOL4:
Theorem nsLookup_add_tenvE2:
   !tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE ∧
    nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE2 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : mlstring) (tvs : Nat)
      (t : sem_t) (tvs2 : Nat),
      tveLookup n tvs tenvE = none ∧
      nsLookup tenvV (.Short n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  intro tenvE tenvV n tvs t tvs2
  induction tenvE generalizing tvs with
  | Empty => intro ⟨_, h⟩; exact h
  | Bind_tvar k e ih =>
    intro ⟨hl, h⟩
    simp only [tveLookup] at hl
    exact ih (tvs + k) ⟨hl, h⟩
  | Bind_name x k t' e ih =>
    intro ⟨hl, h⟩
    simp only [tveLookup] at hl
    simp only [add_tenvE]
    split at hl
    · cases hl
    · rename_i hx
      rw [nsLookup_nsBind.2 _ _ _ _ (by simpa using fun h => hx (by simp [h]))]
      exact ih tvs ⟨hl, h⟩
/- HOL4:
Theorem nsLookup_add_tenvE3:
   !tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE3 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : cml_id modN varN) (t : sem_t)
      (tvs2 : Nat) (mn : modN),
      nsLookup tenvV (.Long mn n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Long mn n) = some (tvs2, t) := by
  intro tenvE tenvV n t tvs2 mn h
  induction tenvE with
  | Empty => exact h
  | Bind_tvar k e ih => exact ih
  | Bind_name x k t' e ih =>
    simp only [add_tenvE]
    rw [nsLookup_nsBind.2 _ _ _ _ (by simp)]
    exact ih
/- HOL4:
Theorem add_tenvE_bvl:
   !n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV)
-/
theorem add_tenvE_bvl :
    ∀ (n : Nat) (bindings : List (mlstring × sem_t)) (tenvE : tenv_val_exp) (tenvV : tenv_val),
      add_tenvE (bind_var_list n bindings tenvE) tenvV =
      nsBindList (bindings.map (fun (x, t) => (x, (n, t)))) (add_tenvE tenvE tenvV) := by
  intro n bindings tenvE tenvV
  induction bindings with
  | nil => rfl
  | cons p bindings ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, add_tenvE, ih]
    rfl
/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t
-/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs tenvC tenvS v_ t → check_freevars tvs [] t := by
  intro tvs tenvC tenvS v_ t h
  induction h with
  | litv_int => simp [Tint]
  | litv_char => simp [Tchar]
  | litv_str => simp [Tstring]
  | litv_word8 => simp [Tword8]
  | litv_word64 => simp [Tword64]
  | litv_float64 => simp [Tdouble]
  | conv_some tvs _ _ ts' _ _ _ _ _ hts => simpa using hts
  | conv_none tvs _ _ vs ts hl _ ih =>
    simp only [Ttup, check_freevars_Tapp, List.all_eq_true]
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    have := ih i (by omega)
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this
  | closure tvs _ _ tenv tenvE env n e t1 t2 hok hE h0 _ _ _ _ _ ht1 he _ =>
    have hbt : num_tvs (bind_tvar tvs tenvE) = tvs ∧ tenv_val_exp_ok (bind_tvar tvs tenvE) := by
      unfold bind_tvar; split <;> simp_all [num_tvs, tenv_val_exp_ok]
    have := type_e_freevars.1 _ _ _ _ he
      ⟨⟨by simpa [hbt.1] using ht1, hbt.2⟩, hok.1⟩
    simp only [num_tvs, hbt.1] at this
    simp [Tfn, ht1, this]
  | recclosure tvs _ _ tenv tenvE env n funs bindings t hok hE h0 _ _ _ _ _ hf hl _ _ _ =>
    have hbt : num_tvs (bind_tvar tvs tenvE) = tvs := by
      unfold bind_tvar; split <;> simp_all [num_tvs]
    obtain ⟨t1, t2, rfl, hc⟩ := type_funs_Tfn _ _ _ _ 0 _ _ ⟨hf, hl⟩
    simpa [num_tvs_bind_var_list, hbt] using hc
  | loc_ref _ _ _ t _ hc => simpa [Tref] using check_freevars_add 0 [] t hc _ (Nat.zero_le _)
  | loc_w8array => simp [Tword8array]
  | loc_varray _ _ _ t _ hc => simpa [Tarray] using check_freevars_add 0 [] t hc _ (Nat.zero_le _)
  | vectorv _ _ _ t _ hc => simpa [Tvector] using check_freevars_add 0 [] t hc _ (Nat.zero_le _)
theorem FUPDATE_LIST_reverse_eq_alist {α β : Type} [BEq α] (l : List (α × β)) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse = Finmap.alist_to_fmap l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [Finmap.FUPDATE_LIST, List.reverse_cons, List.foldl_append, List.foldl] at ih ⊢
    rw [ih]
    funext k
    simp only [Finmap.FUPDATE, Finmap.alist_to_fmap, List.find?]
    split <;> simp_all

theorem ALOOKUP_map_snd_some {α β : Type} [BEq α] (f : β → β) :
    ∀ (l : List (α × β)) (k : α) (v : β), ALOOKUP l k = some v →
      ALOOKUP (l.map (fun (x, t) => (x, f t))) k = some (f v)
  | [], _, _, h => by simp [ALOOKUP] at h
  | (a, b) :: l, k, v, h => by
    simp only [ALOOKUP] at h
    simp only [List.map, ALOOKUP]
    split at h
    · rename_i he; simp only [he]; simp at h; rw [h]; rfl
    · rename_i hne; simp only [hne]; exact ALOOKUP_map_snd_some f l k v h

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (n : Nat)
    (h : n < l.length) : (l.map f)[n]! = f l[n]! := EL_map' f l n h

/- HOL4:
Theorem type_subst:
   !tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t ⇒
     tvs = LENGTH targs ∧
     ctMap_ok ctMap ∧
     EVERY (check_freevars tvs' []) targs ∧
     check_freevars (LENGTH targs) [] t
     ⇒
     type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)
  (with free variables targs and tvs')
-/
theorem type_subst_thm :
    ∀ (targs : List sem_t) (tvs' : Nat),
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs ctMap_ tenvS v_ t →
      tvs = targs.length ∧
      ctMap_ok ctMap_ ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars targs.length [] t →
      type_v tvs' ctMap_ tenvS v_ (deBruijn_subst 0 targs t) := by
  intro targs tvs'' tvs ctMap_ tenvS v_ t h
  have hfvσ : EVERY (check_freevars tvs'' []) targs → ∀ t, check_freevars targs.length [] t →
      check_freevars tvs'' [] (deBruijn_subst 0 targs t) := by
    intro hev t ht
    have := check_freevars_subst _ _ t ht 0 targs tvs'' ⟨by simp, by simpa using hev⟩
    simpa using this
  have hbt : ∀ a E, tenv_val_exp_ok E → tenv_val_exp_ok (bind_tvar a E) := by
    intro a E hE; unfold bind_tvar; split
    · exact hE
    · exact hE
  induction h with
  | litv_int => intro _; simpa [Tint, deBruijn_subst] using type_v.litv_int _ _ _ _
  | litv_char => intro _; simpa [Tchar, deBruijn_subst] using type_v.litv_char _ _ _ _
  | litv_str => intro _; simpa [Tstring, deBruijn_subst] using type_v.litv_str _ _ _ _
  | litv_word8 => intro _; simpa [Tword8, deBruijn_subst] using type_v.litv_word8 _ _ _ _
  | litv_word64 => intro _; simpa [Tword64, deBruijn_subst] using type_v.litv_word64 _ _ _ _
  | litv_float64 => intro _; simpa [Tdouble, deBruijn_subst] using type_v.litv_float64 _ _ _ _
  | conv_some tvs ctMap_ tenvS ts' tvs' vs ts ti stmp hts hlen hvl hall hlk ih =>
    intro ⟨hL, hok, hev, hc⟩
    subst hL
    rw [FUPDATE_LIST_reverse_eq_alist] at hvl hall ih
    have hcl : EVERY (check_freevars 0 tvs') ts := hok.1 stmp _ hlk
    have heq := type_subst_deBruijn_subst_list (.Tvar_db 0) tvs' tvs' ts' targs ts 0 ⟨hlen, hcl⟩
    simp only [ZIP] at heq
    simp only [deBruijn_subst]
    refine .conv_some _ _ _ (ts'.map (deBruijn_subst 0 targs)) tvs' vs ts ti stmp ?_ (by simpa using hlen) ?_ ?_ hlk
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      exact hfvσ hev t0 (hts t0 ht0)
    · rw [FUPDATE_LIST_reverse_eq_alist]; simpa using hvl
    · intro i hi
      rw [FUPDATE_LIST_reverse_eq_alist, ← heq]
      have hi' : i < (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))).length := by
        rw [← hvl]; exact hi
      rw [getElem!_map' _ _ _ hi']
      refine ih i hi ⟨rfl, hok, hev, ?_⟩
      have hi2 : i < ts.length := by simpa using hi'
      rw [getElem!_map' _ _ _ hi2]
      have hmem : ts[i]! ∈ ts := EL_mem' ts i hi2
      have := check_freevars_subst_single targs.length tvs' ts[i]! [] ts'
        ⟨hlen, check_freevars_add _ _ _ (by simp only [EVERY, List.all_eq_true] at hcl; exact hcl _ hmem) _ (Nat.zero_le _),
         by simpa [EVERY] using hts⟩
      simpa [ZIP] using this
  | conv_none tvs ctMap_ tenvS vs ts hl hall ih =>
    intro ⟨hL, hok, hev, hc⟩
    simp only [Ttup, deBruijn_subst]
    refine .conv_none _ _ _ _ _ (by simpa using hl) ?_
    intro i hi
    have hi2 : i < ts.length := by omega
    rw [getElem!_map' _ _ _ hi2]
    refine ih i hi ⟨hL, hok, hev, ?_⟩
    simp only [Ttup, check_freevars_Tapp, List.all_eq_true] at hc
    exact hc _ (EL_mem' ts i hi2)
  | closure tvs ctMap_ tenvS tenv tenvE env n e t1 t2 hok hE h0 hc' hdom hp1 hp2 htyp ht1 he _ =>
    intro ⟨hL, hok', hev, hc⟩
    subst hL
    simp only [Tfn, deBruijn_subst, List.map]
    have he' := type_e_subst_lem n t1 tenv tenvE e t2 targs tvs'' targs
      ⟨he, h0, hok.2.2, hok.2.1, hok.1, hbt _ _ hE, hev, ht1⟩
    exact .closure _ _ _ tenv tenvE env n e _ _ hok hE h0 hc' hdom hp1 hp2 htyp (hfvσ hev t1 ht1) he'
  | recclosure tvs ctMap_ tenvS tenv tenvE env n funs bindings t hok hE h0 hc' hdom hp1 hp2 htyp hf hl hd hm _ =>
    intro ⟨hL, hok', hev, hc⟩
    subst hL
    refine .recclosure _ _ _ tenv tenvE env n funs
      (bindings.map (fun (x, t) => (x, deBruijn_subst 0 targs t))) _ hok hE h0 hc' hdom hp1 hp2 htyp
      ?_ (ALOOKUP_map_snd_some _ _ _ _ hl) hd hm
    have hokb := tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v _ ⟨hf, hbt targs.length _ hE⟩
    have := (type_e_subst tenvE).2.2 tenv _ funs bindings hf (bind_var_list 0 bindings .Empty) targs tvs''
      (targs.map (deBruijn_inc 0 0))
      ⟨h0, hok.2.2, hok.2.1, hok.1, hokb, hev, by rw [db_merge_bvl]; rfl, by simp [num_tvs_bind_var_list, num_tvs]⟩
    rw [deBruijn_subst_E_bvl, db_merge_bvl] at this
    simpa [num_tvs_bind_var_list, num_tvs, deBruijn_subst_tenvE, db_merge, deBruijn_inc0.2] using this
  | loc_ref tvs ctMap_ tenvS t n hc0 hlk =>
    intro _
    simp only [Tref, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    exact .loc_ref _ _ _ _ _ hc0 hlk
  | loc_w8array tvs ctMap_ tenvS n hlk =>
    intro _
    simpa [Tword8array, deBruijn_subst] using type_v.loc_w8array tvs'' _ _ _ hlk
  | loc_varray tvs ctMap_ tenvS t n hc0 hlk =>
    intro _
    simp only [Tarray, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    exact .loc_varray _ _ _ _ _ hc0 hlk
  | vectorv tvs ctMap_ tenvS t vs hc0 hall ih =>
    intro ⟨hL, hok, hev, hc⟩
    simp only [Tvector, deBruijn_subst, List.map, nil_deBruijn_subst 0 targs t hc0]
    refine .vectorv _ _ _ t vs hc0 ?_
    intro w hw
    have := ih w hw ⟨hL, hok, hev, check_freevars_add 0 [] t hc0 _ (Nat.zero_le _)⟩
    rwa [nil_deBruijn_subst 0 targs t hc0] at this
/- HOL4:
Theorem check_ctor_tenv_ok:
 !tenvT tds tis.
 LENGTH tds = LENGTH tis ∧
 check_ctor_tenv tenvT tds ∧
 tenv_abbrev_ok tenvT
 ⇒
 tenv_ctor_ok (build_ctor_tenv tenvT tds tis)
-/
theorem check_ctor_tenv_ok :
    ∀ (tenvT : tenv_abbrev)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tis : List type_ident),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis) := by
  intro tenvT tds
  induction tds with
  | nil => intro tis ⟨hl, _, _⟩; cases tis <;> simp at hl; exact nsAll_nsEmpty _
  | cons td tds ih =>
    intro tis ⟨hl, hc, hok⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tis with
    | nil => simp at hl
    | cons ti tis =>
      simp only [check_ctor_tenv, Bool.and_eq_true, List.all_eq_true] at hc
      obtain ⟨⟨⟨⟨_, _⟩, hcs⟩, _⟩, hc⟩ := hc
      simp only [build_ctor_tenv]
      refine nsAll_nsAppend _ _ _ ⟨ih tis ⟨by simpa using hl, hc, hok⟩, ?_⟩
      apply nsAll_alist_to_ns
      intro p hp
      simp only [List.mem_reverse, List.mem_map] at hp
      obtain ⟨⟨cn, ts⟩, hm, rfl⟩ := hp
      have := hcs (cn, ts) hm
      simp only [Bool.and_eq_true, List.all_eq_true] at this
      simp only [EVERY, List.all_map, List.all_eq_true, Function.comp]
      intro t ht
      exact check_freevars_type_name_subst tvs t 0 tenvT ⟨hok, this.2 t ht, this.1 t ht⟩
theorem mem_zipWith_aux {α β γ : Type} (f : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β) (x : γ), x ∈ List.zipWith f l1 l2 →
      ∃ a ∈ l1, ∃ b ∈ l2, x = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l1, b :: l2, x, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, b, by simp, rfl⟩
    · obtain ⟨a', ha', b', hb', e⟩ := mem_zipWith_aux f l1 l2 x h
      exact ⟨a', by simp [ha'], b', by simp [hb'], e⟩

theorem tenv_val_ok_alist_tenv_add_tvs (tvs : Nat) (bindings : List (mlstring × sem_t))
    (h : ∀ x ∈ bindings, check_freevars tvs [] x.2) :
    tenv_val_ok (alist_to_ns (tenv_add_tvs tvs bindings)) := by
  apply nsAll_alist_to_ns
  intro p hp
  simp only [tenv_add_tvs, List.mem_map] at hp
  obtain ⟨⟨n, t⟩, hm, rfl⟩ := hp
  exact h _ hm

/- HOL4:
Theorem type_d_check_uniq:
 (!check tenv d tdecs new_tenv.
  type_d check tenv d tdecs new_tenv
  ⇒
  type_d F tenv d tdecs new_tenv) ∧
 (!check tenv d tdecs new_tenv.
  type_ds check tenv d tdecs new_tenv
  ⇒
  type_ds F tenv d tdecs new_tenv)
-/
theorem type_d_check_uniq :
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (new_tenv : type_env),
      type_d check tenv d tdecs new_tenv →
      type_d false tenv d tdecs new_tenv) ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident) (new_tenv : type_env),
      type_ds check tenv d tdecs new_tenv →
      type_ds false tenv d tdecs new_tenv) := by
  refine ⟨fun check tenv d tdecs new_tenv h => ?_, fun check tenv d tdecs new_tenv h => ?_⟩
  · refine type_d.rec
      (motive_1 := fun tenv d tdecs new_tenv _ => type_d false tenv d tdecs new_tenv)
      (motive_2 := fun tenv d tdecs new_tenv _ => type_ds false tenv d tdecs new_tenv)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro tenv locs p e tvs t bindings h1 h2 h3 h4 _
      exact .dlet_poly _ _ _ _ _ _ _ _ h1 h2 h3 h4 (fun h => by cases h)
    · intro tenv locs p e t bindings _ h2 h3 h4
      exact .dlet_mono _ _ _ _ _ _ _ (fun h => by cases h) h2 h3 h4
    · intro tenv locs funs tvs bindings h1 _
      exact .dletrec _ _ _ _ _ _ h1 (fun h => by cases h)
    · intro tenv locs tdefs ids tenvT h1 h2 h3 h4 h5
      exact .dtype _ _ _ _ _ _ h1 h2 h3 h4 h5
    · intro tenv locs tvs tn t h1 h2 h3
      exact .dtabbrev _ _ _ _ _ _ h1 h2 h3
    · intro tenv locs cn ts h1 h2
      exact .dexn _ _ _ _ _ h1 h2
    · intro tenv mn ds decls tenv' _ ih
      exact .dmod _ _ _ _ _ _ ih
    · intro tenv lds ds decls1 tenv1 decls2 tenv2 _ _ h3 ih1 ih2
      exact .dlocal _ _ _ _ _ _ _ _ ih1 ih2 h3
    · intro tenv; exact .nil _ _
    · intro tenv d ds decls1 tenv1 decls2 tenv2 _ _ h3 ih1 ih2
      exact .cons _ _ _ _ _ _ _ _ ih1 ih2 h3
  · refine type_ds.rec
      (motive_1 := fun tenv d tdecs new_tenv _ => type_d false tenv d tdecs new_tenv)
      (motive_2 := fun tenv d tdecs new_tenv _ => type_ds false tenv d tdecs new_tenv)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro tenv locs p e tvs t bindings h1 h2 h3 h4 _
      exact .dlet_poly _ _ _ _ _ _ _ _ h1 h2 h3 h4 (fun h => by cases h)
    · intro tenv locs p e t bindings _ h2 h3 h4
      exact .dlet_mono _ _ _ _ _ _ _ (fun h => by cases h) h2 h3 h4
    · intro tenv locs funs tvs bindings h1 _
      exact .dletrec _ _ _ _ _ _ h1 (fun h => by cases h)
    · intro tenv locs tdefs ids tenvT h1 h2 h3 h4 h5
      exact .dtype _ _ _ _ _ _ h1 h2 h3 h4 h5
    · intro tenv locs tvs tn t h1 h2 h3
      exact .dtabbrev _ _ _ _ _ _ h1 h2 h3
    · intro tenv locs cn ts h1 h2
      exact .dexn _ _ _ _ _ h1 h2
    · intro tenv mn ds decls tenv' _ ih
      exact .dmod _ _ _ _ _ _ ih
    · intro tenv lds ds decls1 tenv1 decls2 tenv2 _ _ h3 ih1 ih2
      exact .dlocal _ _ _ _ _ _ _ _ ih1 ih2 h3
    · intro tenv; exact .nil _ _
    · intro tenv d ds decls1 tenv1 decls2 tenv2 _ _ h3 ih1 ih2
      exact .cons _ _ _ _ _ _ _ _ ih1 ih2 h3
/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv')
-/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := by
  intro tenv tenv' ⟨⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩⟩
  exact ⟨nsAll_nsAppend _ _ _ ⟨h1, h1'⟩, nsAll_nsAppend _ _ _ ⟨h2, h2'⟩,
    nsAll_nsAppend _ _ _ ⟨h3, h3'⟩⟩
/- HOL4:
Theorem type_d_tenv_ok_helper:
  (∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv') ∧
  (∀check tenv d tdecs tenv'.
   type_ds check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv')
-/
theorem type_d_tenv_ok_helper :
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_ds check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') := by
  have key : ∀ (check : Bool),
      (∀ (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
        type_d check tenv d tdecs tenv' → tenv_ok tenv → tenv_ok tenv') ∧
      (∀ (tenv : type_env) (d : List dec) (tdecs : Set type_ident) (tenv' : type_env),
        type_ds check tenv d tdecs tenv' → tenv_ok tenv → tenv_ok tenv') := by
    intro check
    have hempty : tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } := tenv_ok_empty
    have m1 := fun tenv d tdecs tenv' (h : type_d check tenv d tdecs tenv') =>
      type_d.rec
      (motive_1 := fun tenv _ _ tenv' _ => tenv_ok tenv → tenv_ok tenv')
      (motive_2 := fun tenv _ _ tenv' _ => tenv_ok tenv → tenv_ok tenv')
      (by
        intro tenv locs p e tvs t bindings _ _ h3 _ _ _
        exact ⟨tenv_val_ok_alist_tenv_add_tvs _ _ (type_p_freevars_aux h3).2,
          nsAll_nsEmpty _, nsAll_nsEmpty _⟩)
      (by
        intro tenv locs p e t bindings _ _ h3 _ _
        exact ⟨tenv_val_ok_alist_tenv_add_tvs _ _ (type_p_freevars_aux h3).2,
          nsAll_nsEmpty _, nsAll_nsEmpty _⟩)
      (by
        intro tenv locs funs tvs bindings h1 _ _
        have := type_funs_freevars_aux h1
        rw [num_tvs_bind_var_list, (bind_tvar_rewrites).2.1] at this
        exact ⟨tenv_val_ok_alist_tenv_add_tvs _ _ (fun x hx => by simpa [num_tvs] using this x hx),
          nsAll_nsEmpty _, nsAll_nsEmpty _⟩)
      (by
        intro tenv locs tdefs ids tenvT _ _ h3 h4 h5 hok
        have hT : tenv_abbrev_ok tenvT := by
          rw [h5]
          apply nsAll_alist_to_ns
          intro p hp
          obtain ⟨⟨tvs, tn, ctors⟩, _, i, _, rfl⟩ := mem_zipWith_aux _ _ _ _ hp
          simp only [check_freevars_Tapp, List.all_map, List.all_eq_true, Function.comp,
            check_freevars_Tvar, List.any_eq_true, beq_iff_eq]
          intro tv htv; exact ⟨tv, htv, rfl⟩
        exact ⟨nsAll_nsEmpty _,
          check_ctor_tenv_ok _ _ _ ⟨h4.symm, h3, nsAll_nsAppend _ _ _ ⟨hT, hok.2.2⟩⟩, hT⟩)
      (by
        intro tenv locs tvs tn t h1 h2 _ hok
        refine ⟨nsAll_nsEmpty _, nsAll_nsEmpty _, ?_⟩
        show tenv_abbrev_ok (alist_to_ns [(tn, (tvs, type_name_subst tenv.t t))])
        apply nsAll_alist_to_ns
        intro p hp; simp at hp; subst hp
        exact check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2, h1⟩)
      (by
        intro tenv locs cn ts h1 h2 hok
        refine ⟨nsAll_nsEmpty _, ?_, nsAll_nsEmpty _⟩
        show tenv_ctor_ok (alist_to_ns [(cn, ([], ts.map (type_name_subst tenv.t), Texn_num))])
        apply nsAll_alist_to_ns
        intro p hp; simp at hp; subst hp
        simp only [EVERY, List.all_map, List.all_eq_true, Function.comp]
        intro t ht
        exact check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2 t ht, h1 t ht⟩)
      (by
        intro tenv mn ds decls tenv' _ ih hok
        have := ih hok
        exact ⟨(nsAll_nsLift _ _ _).2 (fun _ _ h => this.1 _ _ h),
          (nsAll_nsLift _ _ _).2 (fun _ _ h => this.2.1 _ _ h),
          (nsAll_nsLift _ _ _).2 (fun _ _ h => this.2.2 _ _ h)⟩)
      (by
        intro tenv lds ds decls1 tenv1 decls2 tenv2 _ _ _ ih1 ih2 hok
        exact ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩))
      (by intro tenv _; exact hempty)
      (by
        intro tenv d ds decls1 tenv1 decls2 tenv2 _ _ _ ih1 ih2 hok
        have h1 := ih1 hok
        exact extend_dec_tenv_ok _ _ ⟨ih2 (extend_dec_tenv_ok _ _ ⟨h1, hok⟩), h1⟩)
      h
    refine ⟨m1, ?_⟩
    intro tenv ds
    induction ds generalizing tenv with
    | nil => intro tdecs tenv' h _; cases h; exact hempty
    | cons d ds ih =>
      intro tdecs tenv' h hok
      cases h with
      | cons _ _ _ decls1 tenv1 decls2 tenv2 h1 h2 _ =>
        have h1' := m1 _ _ _ _ h1 hok
        exact extend_dec_tenv_ok _ _ ⟨ih _ _ _ h2 (extend_dec_tenv_ok _ _ ⟨h1', hok⟩), h1'⟩
  exact ⟨fun check => (key check).1, fun check => (key check).2⟩
/- HOL4:
Theorem type_d_tenv_ok:
  ∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok (extend_dec_tenv tenv' tenv)
-/
theorem type_d_tenv_ok :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' ∧
      tenv_ok tenv →
      tenv_ok (extend_dec_tenv tenv' tenv) := by
  intro check tenv d tdecs tenv' ⟨h, hok⟩
  exact extend_dec_tenv_ok _ _ ⟨type_d_tenv_ok_helper.1 _ _ _ _ _ h hok, hok⟩
/- HOL4: (commented out)
Theorem type_d_mod -/
-- type_d_mod is commented out in the HOL4 source

/- HOL4:
Theorem type_ds_empty[simp]:
  !check tenv decls r.
  type_ds check tenv [] decls r ⇔
  decls = {} ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |>
-/
theorem type_ds_empty :
    ∀ (check : Bool) (tenv : type_env) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [] decls r ↔
      decls = ∅ ∧ r = { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by
  intro check tenv decls r
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil _ _
/- HOL4:
Theorem type_ds_sing[simp]:
  !check tenv d decls r.
  type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r
-/
theorem type_ds_sing :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := by
  intro check tenv d decls r
  have hu : ∀ (s : Set type_ident), s ∪ ∅ = s := by
    intro s; funext x; apply propext
    show (s x ∨ False) ↔ s x
    simp
  have he : ∀ (t : type_env), extend_dec_tenv { v := nsEmpty, c := nsEmpty, t := nsEmpty } t = t := by
    intro t; simp [extend_dec_tenv, nsAppend_nsEmpty]
  constructor
  · intro h
    cases h with
    | cons _ _ _ decls1 tenv1 decls2 tenv2 h1 h2 _ =>
      cases h2
      rw [hu, he]; exact h1
  · intro h
    have := type_ds.cons _ _ _ _ _ _ _ _ h (type_ds.nil _ _) (fun x hx => hx.2)
    rwa [hu, he] at this
/- HOL4: (commented out)
Theorem type_ds_mod -/
-- type_ds_mod is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_specs_no_mod -/
-- type_specs_no_mod is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_prog_empty -/
-- type_prog_empty is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_prog_sing -/
-- type_prog_sing is commented out in the HOL4 source

/- HOL4: (commented out, tenv_names definition and theorems below are from commented section)
Theorem lookup_tenv_names:
   ∀tenv n inc x. lookup_tenv_val n inc tenv = SOME x ⇒ n ∈ tenv_names tenv
  (uses tveLookup in our translation)
-/
theorem lookup_tenv_names :
    ∀ (tenvE : tenv_val_exp) (n : mlstring) (inc : Nat) (x : Nat × sem_t),
      tveLookup n inc tenvE = some x → n ∈ tenv_names tenvE := by
  intro tenvE n
  induction tenvE with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih => intro inc x h; exact ih _ _ h
  | Bind_name y k t e ih =>
    intro inc x h
    simp only [tveLookup] at h
    show (Set.union (Set.insert y Set.empty) (tenv_names e)) n
    split at h
    · rename_i hy; simp at hy; subst hy; exact Or.inl (Or.inl rfl)
    · exact Or.inr (ih _ _ h)
/- HOL4: (commented out)
Theorem tenv_names_bind_var_list:
   ∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2
-/
theorem tenv_names_bind_var_list :
    ∀ (n : Nat) (l1 : List (mlstring × sem_t)) (l2 : tenv_val_exp),
      tenv_names (bind_var_list n l1 l2) = Set.union (fun x => x ∈ l1.map Prod.fst) (tenv_names l2) := by
  intro n l1 l2
  induction l1 with
  | nil =>
    funext x; apply propext
    show tenv_names l2 x ↔ (x ∈ ([] : List mlstring) ∨ tenv_names l2 x)
    simp
  | cons p l1 ih =>
    obtain ⟨y, t⟩ := p
    funext x; apply propext
    have := congrFun ih x
    show (Set.union (Set.insert y Set.empty) (tenv_names (bind_var_list n l1 l2))) x ↔
      (x ∈ (y :: l1.map Prod.fst) ∨ tenv_names l2 x)
    rw [show (Set.union (Set.insert y Set.empty) (tenv_names (bind_var_list n l1 l2))) x =
      ((x = y ∨ False) ∨ tenv_names (bind_var_list n l1 l2) x) from rfl, this]
    show (x = y ∨ False) ∨ (x ∈ l1.map Prod.fst ∨ tenv_names l2 x) ↔ _
    simp only [or_false, List.mem_cons]
    exact or_assoc.symm
/- HOL4: (commented out, bind_var_list2 not available in Lean)
Theorem tenv_names_bind_var_list2:
   ∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv
  Note: bind_var_list2 is not defined in the Lean translation.
-/
-- tenv_names_bind_var_list2 is not translatable (bind_var_list2 not available)
