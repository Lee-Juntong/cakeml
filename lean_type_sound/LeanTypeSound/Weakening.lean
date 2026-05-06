/-
  Translation of weakeningScript.sml
  Weakening lemmas used in type soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSysProps
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.TypeSoundInvariants

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition weak_tenvE_def:
weak_tenvE tenv tenv' =
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t.
    (tveLookup n inc tenv' = SOME (tvs,t)) ⇔
    (tveLookup n inc tenv = SOME (tvs,t)))
End
-/
def weak_tenvE (tenvE tenvE' : tenv_val_exp) : Prop :=
  num_tvs tenvE ≥ num_tvs tenvE' ∧
  ∀ n inc tvs t,
    (tveLookup n inc tenvE' = some (tvs, t)) ↔
    (tveLookup n inc tenvE = some (tvs, t))

/- HOL4:
Definition weakS_def:
weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
End
-/
def weakS (tenvS tenvS' : tenv_store) : Prop :=
  Finmap.SUBMAP tenvS' tenvS

/- HOL4:
Definition weak_def:
weak tenv' tenv ⇔
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv
End
-/
def weak (tenv' tenv : type_env) : Prop :=
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv

/- HOL4:
Definition weakCT_def:
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl
End
-/
def weakCT (cenv_impl cenv_spec : ctMap) : Prop :=
  Finmap.SUBMAP cenv_spec cenv_impl

-- ============================================================
-- Theorems
-- ============================================================

/- HOL4:
Theorem weak_tenv_refl:
   !tenv. tenv_val_ok tenv.v ⇒ weak_tenv tenv tenv
-/
theorem weak_tenv_refl :
    ∀ (tenv : type_env), tenv_val_ok tenv.v → weak_tenv tenv tenv := sorry
/- HOL4:
Theorem weakS_refl:
   !tenvS. weakS tenvS tenvS
-/
theorem weakS_refl :
    ∀ (tenvS : tenv_store), weakS tenvS tenvS := fun _ _ _ h => h
/- HOL4:
Theorem weak_tenvE_freevars[local]:
  !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t
-/
theorem weak_tenvE_freevars :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : List tvarN) (t : sem_t),
      weak_tenvE tenvE' tenvE ∧ check_freevars (num_tvs tenvE) tvs t →
      check_freevars (num_tvs tenvE') tvs t := sorry
/- HOL4:
Theorem weak_tenvE_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv)
-/
theorem weak_tenvE_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (.Bind_name n tvs t tenvE') (.Bind_name n tvs t tenvE) := sorry
/- HOL4:
Theorem weak_tenvE_opt_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv)
-/
theorem weak_tenvE_opt_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : Option mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (opt_bind_name n tvs t tenvE') (opt_bind_name n tvs t tenvE) := sorry
/- HOL4:
Theorem weak_tenvE_bind_tvar[local]:
  !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)
-/
theorem weak_tenvE_bind_tvar :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar tvs tenvE) := sorry
/- HOL4:
Theorem weak_tenvE_bind_tvar2[local]:
  !tenv tenv' n tvs t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0 ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)
-/
theorem weak_tenvE_bind_tvar2 :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧ weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar 0 tenvE) := sorry
/- HOL4:
Theorem weak_tenvE_bind_var_list[local]:
  !bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)
-/
theorem weak_tenvE_bind_var_list :
    ∀ (bindings : List (mlstring × sem_t)) (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE) := sorry
/- HOL4:
Theorem eLookupC_weak[local]:
  ∀cn tenv tenv' tvs ts tn.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.c cn = SOME (tvs,ts,tn)
    ⇒
    nsLookup tenv'.c cn = SOME (tvs,ts,tn)
-/
theorem eLookupC_weak :
    ∀ (cn : cml_id modN conN) (tenv tenv' : type_env)
      (tvs : List tvarN) (ts : List sem_t) (tn : type_ident),
      weak_tenv tenv' tenv ∧ nsLookup tenv.c cn = some (tvs, ts, tn) →
      nsLookup tenv'.c cn = some (tvs, ts, tn) := sorry
/- HOL4:
Theorem eLookupV_weak[local]:
  ∀n tenv tenv' tvs t.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.v n = SOME (tvs,t)
    ⇒
    ∃tvs' t'. nsLookup tenv'.v n = SOME (tvs',t') ∧ tscheme_inst (tvs,t) (tvs',t')
-/
theorem eLookupV_weak :
    ∀ (n : cml_id modN varN) (tenv tenv' : type_env) (tvs : Nat) (t : sem_t),
      weak_tenv tenv' tenv ∧ nsLookup tenv.v n = some (tvs, t) →
      ∃ (tvs' : Nat) (t' : sem_t),
        nsLookup tenv'.v n = some (tvs', t') ∧ tscheme_inst (tvs, t) (tvs', t') := sorry
/- HOL4:
Theorem type_p_weakening:
 (!tvs tenv p t bindings. type_p tvs tenv p t bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_p tvs' tenv' p t bindings) ∧
 (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_ps tvs' tenv' ps ts bindings)
-/
theorem type_p_weakening :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : sem_t) (bindings : List (varN × sem_t)),
      type_p tvs tenv p t bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t bindings) ∧
    (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List sem_t)
      (bindings : List (varN × sem_t)),
      type_ps tvs tenv ps ts bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts bindings) := sorry
/- HOL4:
Theorem type_e_weakening_lem[local]:
  (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)
-/
theorem type_e_weakening_lem :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp)
      (funs : List (varN × varN × exp)) (bindings : List (varN × sem_t)),
      type_funs tenv tenvE funs bindings →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings) := sorry
/- HOL4:
Theorem type_e_weakening:
 (!tenv tenvE e t tenv' tenvE'.
   type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts tenv' tenvE'.
   type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings tenv' tenvE'.
   type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)
-/
theorem type_e_weakening :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t)
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t)
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp)
      (funs : List (varN × varN × exp)) (bindings : List (varN × sem_t))
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_funs tenv' tenvE' funs bindings) := sorry
/- HOL4:
Theorem gt_0[local]:
  !x:num.x ≥ 0
-/
theorem gt_0 :
    ∀ (x : Nat), x ≥ 0 := fun _ => Nat.zero_le _
/- HOL4:
Theorem weak_ctMap_lookup[local]:
  ∀ctMap ctMap' tvs ts stamp.
  weakCT ctMap' ctMap ∧
  FLOOKUP ctMap stamp = SOME (tvs,ts)
  ⇒
  FLOOKUP ctMap' stamp = SOME (tvs,ts)
-/
theorem weak_ctMap_lookup :
    ∀ (cm cm' : ctMap) (tvs : List tvarN) (ts : List sem_t × type_ident) (stmp : stamp),
      weakCT cm' cm ∧ Finmap.FLOOKUP cm stmp = some (tvs, ts) →
      Finmap.FLOOKUP cm' stmp = some (tvs, ts) := by
  intro cm cm' tvs ts stmp ⟨h1, hlk⟩
  exact h1 stmp (tvs, ts) hlk
/- HOL4:
Theorem weakCT_refl:
 !ctMap. weakCT ctMap ctMap
-/
theorem weakCT_refl :
    ∀ (cm : ctMap), weakCT cm cm := fun _ _ _ h => h
/- HOL4:
Theorem weakCT_trans:
 weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3
-/
theorem weakCT_trans :
    ∀ (C1 C2 C3 : ctMap), weakCT C1 C2 ∧ weakCT C2 C3 → weakCT C1 C3 := by
  intro C1 C2 C3 ⟨h1, h2⟩
  intro k val_ hlk
  exact h1 k val_ (h2 k val_ hlk)
/- HOL4:
Theorem disjoint_env_weakCT:
 !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap
-/
theorem disjoint_env_weakCT :
    ∀ (cm cm' : ctMap),
      Set.Disjoint (Finmap.FDOM cm') (Finmap.FDOM cm) →
      weakCT (Finmap.FUNION cm' cm) cm := by
  intro cm cm' hdisj
  unfold weakCT Finmap.SUBMAP
  intro k val_ hcm
  unfold Finmap.FUNION
  have hk_cm : k ∈ Finmap.FDOM cm := by show (cm k).isSome = true; simp [hcm]
  have hcm'_none : cm' k = none := by
    cases hh : cm' k with
    | none => rfl
    | some v =>
      exfalso
      have hk_cm' : k ∈ Finmap.FDOM cm' := by
        show (cm' k).isSome = true; rw [hh]; rfl
      exact hdisj k ⟨hk_cm', hk_cm⟩
  rw [hcm'_none]; exact hcm
/- HOL4:
Theorem type_tenv_ctor_weakening:
 !ctMap tenvC envC ctMap'.
  weakCT ctMap' ctMap ∧
  nsAll2 (type_ctor ctMap) envC tenvC
  ⇒
  nsAll2 (type_ctor ctMap') envC tenvC
-/
theorem type_tenv_ctor_weakening :
    ∀ (cm : ctMap) (tenvC : tenv_ctor) (envC : env_ctor) (cm' : ctMap),
      weakCT cm' cm ∧ nsAll2 (type_ctor cm) envC tenvC →
      nsAll2 (type_ctor cm') envC tenvC := sorry
/- HOL4:
Theorem type_tenv_val_weakening_lemma[local]:
  !ctMap tenvS tenvV envV ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  nsAll2 (λi v (tvs,t).
          ∀tvs' ctMap' tenvS'.
            (tvs = 0 ∨ tvs = tvs') ∧
            weakCT ctMap' ctMap ∧
            weakS tenvS' tenvS
            ⇒
            type_v tvs' ctMap' tenvS' v t)
         envV tenvV
  ⇒
  nsAll2 (λi v (tvs,t). type_v tvs ctMap' tenvS' v t) envV tenvV
-/
theorem type_tenv_val_weakening_lemma :
    ∀ (cm : ctMap) (tenvS : tenv_store) (tenvV : tenv_val) (envV : env_val)
      (cm' : ctMap) (tenvS' : tenv_store),
      weakCT cm' cm ∧
      weakS tenvS' tenvS ∧
      nsAll2 (fun (i : cml_id modN varN) (val_ : v) (p : Nat × sem_t) =>
        ∀ (tvs' : Nat) (cm'' : ctMap) (tenvS'' : tenv_store),
          (p.1 = 0 ∨ p.1 = tvs') ∧ weakCT cm'' cm ∧ weakS tenvS'' tenvS →
          type_v tvs' cm'' tenvS'' val_ p.2) envV tenvV →
      nsAll2 (fun (_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t) =>
        type_v p.1 cm' tenvS' val_ p.2) envV tenvV := sorry
/- HOL4:
Theorem type_v_weakening:
 (!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'.
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t)
-/
theorem type_v_weakening :
    ∀ (tvs : Nat) (cm : ctMap) (tenvS : tenv_store) (val_ : v) (t : sem_t),
      type_v tvs cm tenvS val_ t →
      ∀ (tvs' : Nat) (cm' : ctMap) (tenvS' : tenv_store),
        (tvs = 0 ∨ tvs = tvs') ∧ weakCT cm' cm ∧ weakS tenvS' tenvS →
        type_v tvs' cm' tenvS' val_ t := sorry
/- HOL4:
Theorem type_all_env_weakening:
 !ctMap tenvS tenv env ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  type_all_env ctMap tenvS env tenv
  ⇒
  type_all_env ctMap' tenvS' env tenv
-/
theorem type_all_env_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (tenv : type_env) (env : sem_env)
      (cm' : ctMap) (tenvS' : tenv_store),
      weakCT cm' cm ∧ weakS tenvS' tenvS ∧ type_all_env cm tenvS env tenv →
      type_all_env cm' tenvS' env tenv := sorry
/- HOL4:
Theorem type_sv_weakening:
 !ctMap tenvS st sv ctMap' tenvS'.
  type_sv ctMap tenvS sv st ∧
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS
  ⇒
  type_sv ctMap' tenvS' sv st
-/
theorem type_sv_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (st : store_t) (sv : store_v v)
      (cm' : ctMap) (tenvS' : tenv_store),
      type_sv cm tenvS sv st ∧ weakCT cm' cm ∧ weakS tenvS' tenvS →
      type_sv cm' tenvS' sv st := sorry
/- HOL4:
Theorem type_s_weakening:
 !ctMap tenvS st ctMap'.
  type_s ctMap tenvS st ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' tenvS st
-/
theorem type_s_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (st : store v) (cm' : ctMap),
      type_s cm st tenvS ∧ weakCT cm' cm →
      type_s cm' st tenvS := sorry
/- HOL4:
Theorem weak_tenv_extend_dec_tenv:
   !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3)
-/
theorem weak_tenv_extend_dec_tenv :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      tenv_val_ok tenv1.v ∧ weak_tenv tenv2 tenv3 →
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := sorry
