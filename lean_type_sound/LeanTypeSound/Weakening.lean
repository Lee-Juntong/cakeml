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
    ∀ (tenv : type_env), tenv_val_ok tenv.v → weak_tenv tenv tenv := by
  intro tenv hv
  refine ⟨nsSub_refl (fun (_ : cml_id modN varN) (p : Nat × sem_t) => check_freevars p.1 [] p.2) _ ?_ _ hv,
    nsSub_refl (fun _ _ => True) _ (fun _ _ _ => rfl) _ (fun _ _ _ => trivial)⟩
  intro _ p hp
  obtain ⟨tvs, t⟩ := p
  refine ⟨GENLIST (fun i => sem_t.Tvar_db i) tvs, by simp [GENLIST], hp, ?_, ?_⟩
  · intro s hs
    simp only [GENLIST, List.mem_map, List.mem_range] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    simpa using hi
  · exact deBruijn_subst_id.1 t tvs hp
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
      check_freevars (num_tvs tenvE') tvs t := by
  intro tenvE tenvE' tvs t ⟨⟨hn, _⟩, hc⟩
  exact check_freevars_add _ _ _ hc _ hn
/- HOL4:
Theorem weak_tenvE_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv)
-/
theorem weak_tenvE_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (.Bind_name n tvs t tenvE') (.Bind_name n tvs t tenvE) := by
  intro tenvE tenvE' n tvs t ⟨hn, hl⟩
  refine ⟨by simpa [num_tvs] using hn, ?_⟩
  intro x inc tvs' t'
  simp only [tveLookup]
  split
  · exact Iff.rfl
  · exact hl x inc tvs' t'
/- HOL4:
Theorem weak_tenvE_opt_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv)
-/
theorem weak_tenvE_opt_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : Option mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (opt_bind_name n tvs t tenvE') (opt_bind_name n tvs t tenvE) := by
  intro tenvE tenvE' n tvs t h
  cases n with
  | none => exact h
  | some n => exact weak_tenvE_bind _ _ _ _ _ h
/- HOL4:
Theorem weak_tenvE_bind_tvar[local]:
  !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)
-/
theorem weak_tenvE_bind_tvar :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar tvs tenvE) := by
  intro tenvE tenvE' tvs ⟨hn, hl⟩
  refine ⟨by simp only [bind_tvar_rewrites.2.1]; omega, ?_⟩
  intro x inc tvs' t'
  simp only [bind_tvar_rewrites.2.2.2.2.2.1]
  exact hl x (inc + tvs) tvs' t'
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
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar 0 tenvE) := by
  intro tenvE tenvE' tvs ⟨hok, hn0, hn, hl⟩
  refine ⟨by simp only [bind_tvar_rewrites.2.1]; omega, ?_⟩
  intro x inc tvs' t'
  simp only [bind_tvar_rewrites.2.2.2.2.2.1, bind_tvar0]
  rw [← hl x (inc + tvs) tvs' t', tveLookup_no_tvs inc tvs' tenvE x t' ⟨hok, hn0⟩,
    tveLookup_no_tvs (inc + tvs) tvs' tenvE x t' ⟨hok, hn0⟩]
/- HOL4:
Theorem weak_tenvE_bind_var_list[local]:
  !bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)
-/
theorem weak_tenvE_bind_var_list :
    ∀ (bindings : List (mlstring × sem_t)) (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE) := by
  intro bindings tenvE tenvE' tvs h
  induction bindings with
  | nil => exact h
  | cons p bindings ih =>
    obtain ⟨x, t⟩ := p
    exact weak_tenvE_bind _ _ _ _ _ ih
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
      nsLookup tenv'.c cn = some (tvs, ts, tn) := by
  intro cn tenv tenv' tvs ts tn ⟨⟨_, hc⟩, hl⟩
  obtain ⟨v2, h2, e⟩ := hc.1 _ _ hl
  rw [h2, ← e]
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
        nsLookup tenv'.v n = some (tvs', t') ∧ tscheme_inst (tvs, t) (tvs', t') := by
  intro n tenv tenv' tvs t ⟨⟨hv, _⟩, hl⟩
  obtain ⟨⟨tvs', t'⟩, h2, hi⟩ := hv.1 _ _ hl
  exact ⟨tvs', t', h2, hi⟩
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
        tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts bindings) := by
  have hp : ∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : sem_t) (bindings : List (varN × sem_t)),
      type_p tvs tenv p t bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t bindings := by
    intro tvs tenv p t bindings h
    refine type_p.rec
      (motive_1 := fun p t bindings _ => ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t bindings)
      (motive_2 := fun ps ts bindings _ => ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts bindings)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro t hc tenv' tvs' ⟨hge, _⟩
      exact .pany _ _ _ (check_freevars_add _ _ _ hc _ hge)
    · intro n t hc tenv' tvs' ⟨hge, _⟩
      exact .pvar _ _ _ _ (check_freevars_add _ _ _ hc _ hge)
    · intro _ _ _ _; exact .plit_int _ _ _
    · intro _ _ _ _; exact .plit_char _ _ _
    · intro _ _ _ _; exact .plit_str _ _ _
    · intro _ _ _ _; exact .plit_word8 _ _ _
    · intro _ _ _ _; exact .plit_word64 _ _ _
    · intro cn ps ts' tvs'' ts tn bindings h1 h2 _ h4 ih tenv' tvs' ⟨hge, hw⟩
      exact .pcon_some _ _ _ _ _ _ _ _ _ (fun t ht => check_freevars_add _ _ _ (h1 t ht) _ hge)
        h2 (ih tenv' tvs' ⟨hge, hw⟩) (eLookupC_weak _ _ _ _ _ _ ⟨hw.2, h4⟩)
    · intro ps ts bindings _ ih tenv' tvs' hh
      exact .pcon_none _ _ _ _ _ (ih tenv' tvs' hh)
    · intro p t bindings _ ih tenv' tvs' hh
      exact .pref _ _ _ _ _ (ih tenv' tvs' hh)
    · intro p t bindings v_ _ ih tenv' tvs' hh
      exact .pas _ _ _ _ _ _ (ih tenv' tvs' hh)
    · intro p t bindings h1 h2 _ ih tenv' tvs' ⟨hge, hw⟩
      have := ih tenv' tvs' ⟨hge, hw⟩
      rw [← hw.1] at this h2 ⊢
      exact .ptannot _ _ _ _ _ h1 h2 this
    · intro _ _ _; exact .nil _ _
    · intro p t bindings ps ts bindings' _ _ ih1 ih2 tenv' tvs' hh
      exact .cons _ _ _ _ _ _ _ _ (ih1 tenv' tvs' hh) (ih2 tenv' tvs' hh)
  refine ⟨hp, ?_⟩
  intro tvs tenv ps
  induction ps with
  | nil => intro ts bindings h tenv' tvs' _; cases h; exact .nil _ _
  | cons p ps ih =>
    intro ts bindings h tenv' tvs' hh
    cases h with
    | cons _ t b _ ts' b' h1 h2 =>
      exact .cons _ _ _ _ _ _ _ _ (hp _ _ _ _ _ h1 tenv' tvs' hh) (ih _ _ h2 tenv' tvs' hh)
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
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings) := by
  have main : ∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t := by
    intro tenv tenvE e t h
    refine type_e.rec
      (motive_1 := fun tenvE e t _ => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t)
      (motive_2 := fun tenvE es ts _ => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts)
      (motive_3 := fun tenvE funs bindings _ => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro _ _ _ _ _; exact .lit_int _ _ _
    · intro _ _ _ _ _; exact .lit_char _ _ _
    · intro _ _ _ _ _; exact .lit_str _ _ _
    · intro _ _ _ _ _; exact .lit_word8 _ _ _
    · intro _ _ _ _ _; exact .lit_word64 _ _ _
    · intro _ _ _ _ _; exact .lit_float64 _ _ _
    · intro tenvE e t h1 _ ih tenv' tenvE' ⟨hw, hwe⟩
      exact .raise _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hwe, h1⟩) (ih _ _ ⟨hw, hwe⟩)
    · intro tenvE e t pes bindings_of _ hne hd hp _ ih1 ih2 tenv' tenvE' ⟨hw, hwe⟩
      refine .handle _ _ _ _ _ bindings_of (ih1 _ _ ⟨hw, hwe⟩) hne hd ?_ ?_
      · intro pe hpe
        exact type_p_weakening.1 _ _ _ _ _ (hp pe hpe) _ _ ⟨hwe.1, hw⟩
      · intro pe hpe
        exact ih2 pe hpe _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ _ hwe⟩
    · intro tenvE cn es ts' tvs ts tn h1 h2 _ h4 ih tenv' tenvE' ⟨hw, hwe⟩
      exact .con_some _ _ _ _ _ _ _ _
        (fun t ht => weak_tenvE_freevars _ _ _ _ ⟨hwe, h1 t ht⟩) h2 (ih _ _ ⟨hw, hwe⟩)
        (eLookupC_weak _ _ _ _ _ _ ⟨hw.2, h4⟩)
    · intro tenvE es ts _ ih tenv' tenvE' hh
      exact .con_none _ _ _ _ (ih _ _ hh)
    · intro tenvE n tvs t targs h1 h2 h3 tenv' tenvE' ⟨hw, hwe⟩
      have h2' : ∀ ta ∈ targs, check_freevars (num_tvs tenvE') [] ta :=
        fun ta hta => weak_tenvE_freevars _ _ _ _ ⟨hwe, h2 ta hta⟩
      simp only [lookup_var] at h3
      cases hx : lookup_varE n tenvE with
      | some p =>
        rw [hx] at h3; cases h3
        refine .var _ _ _ _ _ _ h1 h2' ?_
        simp only [lookup_var]
        have : lookup_varE n tenvE' = some (tvs, t) := by
          cases n with
          | Short x =>
            simp only [lookup_varE] at hx ⊢
            exact (hwe.2 x 0 tvs t).1 hx
          | Long _ _ => simp [lookup_varE] at hx
        rw [this]
      | none =>
        rw [hx] at h3
        simp only at h3
        have hx' : lookup_varE n tenvE' = none := by
          cases n with
          | Short x =>
            simp only [lookup_varE] at hx ⊢
            cases hq : tveLookup x 0 tenvE' with
            | none => rfl
            | some q =>
              obtain ⟨q1, q2⟩ := q
              rw [(hwe.2 x 0 q1 q2).2 hq] at hx; cases hx
          | Long _ _ => rfl
        obtain ⟨tvs', t', hl', hi⟩ := eLookupV_weak _ _ _ _ _ ⟨hw.2, h3⟩
        obtain ⟨sub, hsl, hc', hsc, hse⟩ := hi
        have e := deBruijn_subst2_thm.1 t' 0 sub targs [] (by rw [hsl]; exact hc')
        rw [deBruijn_inc0.2] at e
        rw [← hse, e]
        refine .var tenv' tenvE' n tvs' t' (sub.map (deBruijn_subst 0 targs)) (by simp [hsl]) ?_ ?_
        · intro ta hta
          simp only [List.mem_map] at hta
          obtain ⟨s, hs, rfl⟩ := hta
          exact deBruijn_subst_check_freevars2 _ [] s targs 0 []
            ⟨by rw [← h1]; exact hsc s hs, by simpa [EVERY] using h2'⟩
        · simp only [lookup_var, hx', hl']
    · intro tenvE n e t1 t2 h1 _ ih tenv' tenvE' ⟨hw, hwe⟩
      exact .fun_ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hwe, h1⟩)
        (ih _ _ ⟨hw, weak_tenvE_bind _ _ _ _ _ hwe⟩)
    · intro tenvE o es ts t _ h2 h3 ih tenv' tenvE' ⟨hw, hwe⟩
      exact .app _ _ _ _ _ _ (ih _ _ ⟨hw, hwe⟩) h2 (weak_tenvE_freevars _ _ _ _ ⟨hwe, h3⟩)
    · intro tenvE l e1 e2 _ _ ih1 ih2 tenv' tenvE' hh
      exact .log _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh)
    · intro tenvE e1 e2 e3 t _ _ _ ih1 ih2 ih3 tenv' tenvE' hh
      exact .if_ _ _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh) (ih3 _ _ hh)
    · intro tenvE e t1 t2 pes bindings_of _ hne hd hp _ ih1 ih2 tenv' tenvE' ⟨hw, hwe⟩
      refine .mat _ _ _ _ _ _ bindings_of (ih1 _ _ ⟨hw, hwe⟩) hne hd ?_ ?_
      · intro pe hpe
        exact type_p_weakening.1 _ _ _ _ _ (hp pe hpe) _ _ ⟨hwe.1, hw⟩
      · intro pe hpe
        exact ih2 pe hpe _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ _ hwe⟩
    · intro tenvE n e1 t1 e2 t2 _ _ ih1 ih2 tenv' tenvE' ⟨hw, hwe⟩
      exact .let_ _ _ _ _ _ _ _ (ih1 _ _ ⟨hw, hwe⟩)
        (ih2 _ _ ⟨hw, weak_tenvE_opt_bind _ _ _ _ _ hwe⟩)
    · intro tenvE funs bindings e t _ _ ih1 ih2 tenv' tenvE' ⟨hw, hwe⟩
      exact .letrec _ _ _ _ _ _ (ih1 _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ _ hwe⟩)
        (ih2 _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ _ hwe⟩)
    · intro tenvE e t h1 h2 _ ih tenv' tenvE' ⟨hw, hwe⟩
      have := ih _ _ ⟨hw, hwe⟩
      rw [← hw.1] at this h2 ⊢
      exact .tannot _ _ _ _ h1 h2 this
    · intro tenvE e t l _ ih tenv' tenvE' hh
      exact .lannot _ _ _ _ _ (ih _ _ hh)
    · intro _ _ _ _; exact .nil _ _
    · intro tenvE e t es ts _ _ ih1 ih2 tenv' tenvE' hh
      exact .cons _ _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh)
    · intro _ _ _ _; exact .nil _ _
    · intro tenvE fn n e t1 t2 funs bindings h1 _ _ h4 ih1 ih2 tenv' tenvE' ⟨hw, hwe⟩
      exact .cons _ _ _ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hwe, h1⟩)
        (ih1 _ _ ⟨hw, weak_tenvE_bind _ _ _ _ _ hwe⟩) (ih2 _ _ ⟨hw, hwe⟩) h4
  refine ⟨main, ?_, ?_⟩
  · intro tenv tenvE es
    induction es with
    | nil => intro ts h _ _ _; cases h; exact .nil _ _
    | cons e es ih =>
      intro ts h tenv' tenvE' hh
      cases h with
      | cons _ _ t _ ts h1 h2 => exact .cons _ _ _ _ _ _ (main _ _ _ _ h1 _ _ hh) (ih _ h2 _ _ hh)
  · intro tenv tenvE funs
    induction funs generalizing tenvE with
    | nil => intro bindings h _ _ _; cases h; exact .nil _ _
    | cons f funs ih =>
      intro bindings h tenv' tenvE' ⟨hw, hwe⟩
      cases h with
      | cons _ fn n e t1 t2 _ bindings h1 h2 h3 h4 =>
        exact .cons _ _ _ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hwe, h1⟩)
          (main _ _ _ _ h2 _ _ ⟨hw, weak_tenvE_bind _ _ _ _ _ hwe⟩) (ih _ _ h3 _ _ ⟨hw, hwe⟩) h4
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
      type_funs tenv' tenvE' funs bindings) := by
  refine ⟨fun tenv tenvE e t tenv' tenvE' ⟨h, hw, hwe⟩ =>
      type_e_weakening_lem.1 _ _ _ _ h _ _ ⟨hw, hwe⟩,
    fun tenv tenvE es ts tenv' tenvE' ⟨h, hw, hwe⟩ =>
      type_e_weakening_lem.2.1 _ _ _ _ h _ _ ⟨hw, hwe⟩,
    fun tenv tenvE funs b tenv' tenvE' ⟨h, hw, hwe⟩ =>
      type_e_weakening_lem.2.2 _ _ _ _ h _ _ ⟨hw, hwe⟩⟩
/- HOL4:
Theorem gt_0[local]:
  !x:num.x ≥ 0
-/
theorem gt_0 :
    ∀ (x : Nat), x ≥ 0 := fun x => Nat.zero_le x
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
  intro cm cm' tvs ts stmp ⟨h, hl⟩
  exact h _ _ hl
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
  intro C1 C2 C3 ⟨h1, h2⟩ k v hk
  exact h1 _ _ (h2 _ _ hk)
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
  intro cm cm' hd k v hk
  simp only [Finmap.FUNION]
  cases h : cm' k with
  | none => exact hk
  | some v' =>
    exfalso
    exact hd k ⟨by simp [Finmap.FDOM, h], by simp [Finmap.FDOM, hk]⟩
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
      nsAll2 (type_ctor cm') envC tenvC := by
  intro cm tenvC envC cm' ⟨hw, h⟩
  exact nsAll2_mono (fun _ x y ⟨h1, h2⟩ => ⟨hw _ _ h1, h2⟩) h
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
        type_v p.1 cm' tenvS' val_ p.2) envV tenvV := by
  intro cm tenvS tenvV envV cm' tenvS' ⟨hc, hs, h⟩
  exact nsAll2_mono (fun _ v p hp => hp p.1 cm' tenvS' ⟨Or.inr rfl, hc, hs⟩) h
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
        type_v tvs' cm' tenvS' val_ t := by
  intro tvs cm tenvS val_ t h
  induction h with
  | litv_int => intros; exact .litv_int _ _ _ _
  | litv_char => intros; exact .litv_char _ _ _ _
  | litv_str => intros; exact .litv_str _ _ _ _
  | litv_word8 => intros; exact .litv_word8 _ _ _ _
  | litv_word64 => intros; exact .litv_word64 _ _ _ _
  | litv_float64 => intros; exact .litv_float64 _ _ _ _
  | conv_some tvs cm tenvS ts' tvs'' vs ts ti stmp h1 h2 h3 _ h5 ih =>
    intro tvs' cm' tenvS' ⟨htv, hc, hs⟩
    refine .conv_some _ _ _ _ _ _ _ _ _ ?_ h2 h3 (fun i hi => ih i hi tvs' cm' tenvS' ⟨htv, hc, hs⟩)
      (hc _ _ h5)
    intro t ht
    rcases htv with rfl | rfl
    · exact check_freevars_add _ _ _ (h1 t ht) _ (Nat.zero_le _)
    · exact h1 t ht
  | conv_none tvs cm tenvS vs ts h1 _ ih =>
    intro tvs' cm' tenvS' hh
    exact .conv_none _ _ _ _ _ h1 (fun i hi => ih i hi tvs' cm' tenvS' hh)
  | closure tvs cm tenvS tenv tenvE env n e t1 t2 h1 h2 h3 h4 h5 h6 h7 _ h9 h10 ih =>
    intro tvs' cm' tenvS' ⟨htv, hc, hs⟩
    refine .closure _ _ _ tenv tenvE _ _ _ _ _ h1 h2 h3 (type_tenv_ctor_weakening _ _ _ _ ⟨hc, h4⟩)
      h5 h6 h7 (fun id_ val_ p hv hp => ih id_ val_ p hv hp p.1 cm' tenvS' ⟨Or.inr rfl, hc, hs⟩)
      ?_ ?_
    · rcases htv with rfl | rfl
      · exact check_freevars_add _ _ _ h9 _ (Nat.zero_le _)
      · exact h9
    · rcases htv with rfl | rfl
      · refine type_e_weakening.1 _ _ _ _ _ _ ⟨h10, ⟨rfl, weak_tenv_refl _ h1.1⟩, ?_⟩
        apply weak_tenvE_bind
        exact weak_tenvE_bind_tvar2 _ _ _ ⟨h2, h3, ⟨Nat.le_refl _, fun _ _ _ _ => Iff.rfl⟩⟩
      · exact h10
  | recclosure tvs cm tenvS tenv tenvE env n funs bindings t h1 h2 h3 h4 h5 h6 h7 _ h9 h10 h11 h12
      ih =>
    intro tvs' cm' tenvS' ⟨htv, hc, hs⟩
    refine .recclosure _ _ _ tenv tenvE _ _ _ _ _ h1 h2 h3 (type_tenv_ctor_weakening _ _ _ _ ⟨hc, h4⟩)
      h5 h6 h7 (fun id_ val_ p hv hp => ih id_ val_ p hv hp p.1 cm' tenvS' ⟨Or.inr rfl, hc, hs⟩)
      ?_ h10 h11 h12
    rcases htv with rfl | rfl
    · refine type_e_weakening.2.2 _ _ _ _ _ _ ⟨h9, ⟨rfl, weak_tenv_refl _ h1.1⟩, ?_⟩
      apply weak_tenvE_bind_var_list
      exact weak_tenvE_bind_tvar2 _ _ _ ⟨h2, h3, ⟨Nat.le_refl _, fun _ _ _ _ => Iff.rfl⟩⟩
    · exact h9
  | loc_ref tvs cm tenvS t n h1 h2 =>
    intro tvs' cm' tenvS' ⟨_, _, hs⟩
    exact .loc_ref _ _ _ _ _ h1 (hs _ _ h2)
  | loc_w8array tvs cm tenvS n h1 =>
    intro tvs' cm' tenvS' ⟨_, _, hs⟩
    exact .loc_w8array _ _ _ _ (hs _ _ h1)
  | loc_varray tvs cm tenvS t n h1 h2 =>
    intro tvs' cm' tenvS' ⟨_, _, hs⟩
    exact .loc_varray _ _ _ _ _ h1 (hs _ _ h2)
  | vectorv tvs cm tenvS t vs h1 _ ih =>
    intro tvs' cm' tenvS' hh
    exact .vectorv _ _ _ _ _ h1 (fun w hw => ih w hw tvs' cm' tenvS' hh)
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
      type_all_env cm' tenvS' env tenv := by
  intro cm tenvS tenv env cm' tenvS' ⟨hc, hs, h1, h2⟩
  exact ⟨type_tenv_ctor_weakening _ _ _ _ ⟨hc, h1⟩,
    nsAll2_mono (fun _ v p hp => type_v_weakening _ _ _ _ _ hp _ _ _ ⟨Or.inr rfl, hc, hs⟩) h2⟩
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
      type_sv cm' tenvS' sv st := by
  intro cm tenvS st sv cm' tenvS' ⟨h, hc, hs⟩
  cases sv <;> cases st <;> simp only [type_sv] at h ⊢
  · exact type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inl rfl, hc, hs⟩
  · exact fun w hw => type_v_weakening _ _ _ _ _ (h w hw) _ _ _ ⟨Or.inl rfl, hc, hs⟩
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
      type_s cm' st tenvS := by
  intro cm tenvS st cm' ⟨h, hc⟩ l
  refine ⟨(h l).1, fun st' sv hh => ?_⟩
  exact type_sv_weakening _ _ _ _ _ _ ⟨(h l).2 st' sv hh, hc, weakS_refl _⟩
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
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := by
  intro tenv1 tenv2 tenv3 ⟨hv, hv2, hc2⟩
  refine ⟨nsSub_nsAppend2 _ _ _ _ ⟨?_, hv2⟩, nsSub_nsAppend2 _ _ _ _ ⟨?_, hc2⟩⟩
  · exact (weak_tenv_refl tenv1 hv).1
  · exact nsSub_refl (fun _ _ => True) _ (fun _ _ _ => rfl) _ (fun _ _ _ => trivial)
