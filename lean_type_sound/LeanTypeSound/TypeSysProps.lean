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

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv
-/
theorem unchanged_tenv :
    ∀ (tenv : type_env),
      { v := tenv.v, c := tenv.c, t := tenv.t : type_env} = tenv := by
  intro tenv; rfl
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
  simp [extend_dec_tenv]
  refine ⟨?_, ?_, ?_⟩ <;> exact (nsAppend_assoc _ _ _)
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
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } :=
  ⟨tenv_val_ok_nsEmpty, tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩
/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)
-/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := sorry
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
      check_freevars dbmax tvs' (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))) t) := sorry
/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)
-/
theorem deBruijn_inc0 :
    (∀ (t : sem_t) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List sem_t) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := sorry
/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t
-/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := sorry
/- HOL4: [local]
Theorem deBuijn_inc_lem1:
  !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t
-/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t := sorry
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
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t)))) t := sorry
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
      ts'.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t))))) := sorry
/- HOL4: [local]
Theorem check_freevars_deBruijn_inc:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)
-/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := sorry
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
      deBruijn_inc skip tvs t = t := sorry
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
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := sorry
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
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := sorry
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
          (deBruijn_subst 0 targs (deBruijn_inc targs.length tvs1 t)) := sorry
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
        check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := sorry
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
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t)))) t := sorry
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
      ts''.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t))))) := sorry
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
          (deBruijn_subst n1 (targs.map (deBruijn_inc 0 n1)) t) := sorry
/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)
-/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List sem_t) (t : sem_t),
      check_freevars skip [] t →
      deBruijn_subst skip tvs t = t := sorry
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
      ts.map (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := sorry
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
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) := sorry
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
      (ts.map (deBruijn_inc n inc)).map (deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n'))))) := sorry
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
      ts'.map (deBruijn_inc 0 inc)) := sorry
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
        (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := sorry
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
      ts.map (deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n)) = ts) := sorry
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
      check_freevars tvs [] (deBruijn_subst skip targs t) := sorry
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
      check_freevars 0 tvs t := sorry
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
      check_freevars dbmax tvs (type_name_subst tenvT t) := sorry
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
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) := sorry
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
      EVERY (check_freevars 0 tvs) ts := sorry
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
      bind_tvar tvs (deBruijn_subst_tenvE targs e)) := sorry
/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x
-/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  intro x; rfl
/- HOL4:
Theorem tveLookup_subst_none:
 !n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE
-/
theorem tveLookup_subst_none :
    ∀ (targs : List sem_t) (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
      tveLookup n inc e = none := sorry
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
      tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none := sorry
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
      tveLookup n 0 e = none := sorry
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
      check_freevars tvs' [] t := sorry
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
      check_freevars (tvs + inc + num_tvs e) [] t := sorry
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
  | cons p ps ih =>
    obtain ⟨x, t⟩ := p
    simp [bind_var_list, ih]
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
  | cons p ps ih =>
    obtain ⟨x, t⟩ := p
    simp [bind_var_list, num_tvs, ih]
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
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := sorry
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
          (targs.map (deBruijn_inc 0 (tvs + inc + num_tvs e))) t) := sorry
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
  | Bind_tvar tvs e ih => simp [db_merge, num_tvs, ih]; omega
  | Bind_name n tvs t e ih => simp [db_merge, num_tvs, ih]
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
  | Bind_tvar tvs e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
  | Bind_name n tvs t e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
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
        tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t') := sorry
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
      check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := sorry
/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2
-/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp),
      tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := sorry
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
       tveLookup n 0 tenv = some (l, t)) := sorry
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
        (deBruijn_subst_tenvE targs tenv2) := sorry
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
  | cons p ps ih =>
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
       tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t)) := sorry
/- HOL4:
Theorem type_op_cases:
  (computed/derived theorem: expands type_op into disjunctive normal form)
  In Lean, this is the definitional unfolding of type_op.
-/
theorem type_op_cases_thm :
    ∀ (op_ : op) (ts : List sem_t) (t3 : sem_t),
      type_op op_ ts t3 ↔ type_op op_ ts t3 := by
  intros; rfl
/- HOL4:
Theorem type_ps_length:
 ∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)
-/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (tenv : List (varN × sem_t)),
      type_ps tvs tenvC ps ts tenv → ps.length = ts.length := sorry
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
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) := sorry
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
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := sorry
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
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := sorry
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
      type_ps tvs tenv ps t bindings = type_ps tvs { tenv with v := tenvV } ps t bindings) := sorry
/- HOL4:
Theorem type_es_list_rel:
 !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts
-/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List sem_t) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts := sorry
/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts)
-/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts → es.length = ts.length := sorry
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
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := sorry
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
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := sorry
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
          funs (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1) targs' t)))) := sorry
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
      ∃ (t1 t2 : sem_t), t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := sorry
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
      ∃ (t : sem_t), ALOOKUP bindings fn = some t := sorry
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
      ∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e) := sorry
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
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := sorry
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
      ALL_DISTINCT (funs.map (fun (x, _, _) => x)) := sorry
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
        e (deBruijn_subst 0 targs t) := sorry
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
      ∃ (cn : conN) (i : Nat), stmp = .TypeStamp cn i ∧ next ≤ i ∧ i < next + tds.length := sorry
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
      ctMap_ok (Finmap.FUNION ctMap1 ctMap2) := sorry
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
      EVERY (check_freevars 0 tvs) ts := sorry
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
      x.2.2 ∈ tids := sorry
/- HOL4: [local]
Theorem fupdate2_union:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1)
-/
theorem fupdate2_union :
    ∀ (m : Finmap stamp (List tvarN × List sem_t × type_ident))
      (a1 a2 : List (stamp × (List tvarN × List sem_t × type_ident))),
      Finmap.FUPDATE_LIST (Finmap.FUPDATE_LIST m a1) a2 =
      Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY a2) (Finmap.FUPDATE_LIST m a1) := sorry
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
      ctMap_ok (Finmap.FUPDATE_LIST Finmap.FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse) := sorry
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
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := sorry
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
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := sorry
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
      nsLookup (add_tenvE tenvE tenvV) (.Long mn n) = some (tvs2, t) := sorry
/- HOL4:
Theorem add_tenvE_bvl:
   !n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV)
-/
theorem add_tenvE_bvl :
    ∀ (n : Nat) (bindings : List (mlstring × sem_t)) (tenvE : tenv_val_exp) (tenvV : tenv_val),
      add_tenvE (bind_var_list n bindings tenvE) tenvV =
      nsBindList (bindings.map (fun (x, t) => (x, (n, t)))) (add_tenvE tenvE tenvV) := sorry
/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t
-/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs tenvC tenvS v_ t → check_freevars tvs [] t := sorry
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
      type_v tvs' ctMap_ tenvS v_ (deBruijn_subst 0 targs t) := sorry
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
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis) := sorry
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
      type_ds false tenv d tdecs new_tenv) := sorry
/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv')
-/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := sorry
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
      tenv_ok tenv') := sorry
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
      tenv_ok (extend_dec_tenv tenv' tenv) := sorry
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
      decls = ∅ ∧ r = { v := nsEmpty, c := nsEmpty, t := nsEmpty } := sorry
/- HOL4:
Theorem type_ds_sing[simp]:
  !check tenv d decls r.
  type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r
-/
theorem type_ds_sing :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := sorry
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
      tveLookup n inc tenvE = some x → n ∈ tenv_names tenvE := sorry
/- HOL4: (commented out)
Theorem tenv_names_bind_var_list:
   ∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2
-/
theorem tenv_names_bind_var_list :
    ∀ (n : Nat) (l1 : List (mlstring × sem_t)) (l2 : tenv_val_exp),
      tenv_names (bind_var_list n l1 l2) = Set.union (fun x => x ∈ l1.map Prod.fst) (tenv_names l2) := sorry
/- HOL4: (commented out, bind_var_list2 not available in Lean)
Theorem tenv_names_bind_var_list2:
   ∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv
  Note: bind_var_list2 is not defined in the Lean translation.
-/
-- tenv_names_bind_var_list2 is not translatable (bind_var_list2 not available)
