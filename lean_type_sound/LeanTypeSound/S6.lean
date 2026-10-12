import LeanTypeSound.TypeSound
open HOL4

/-- The conclusion of declaration soundness. -/
def DecResult {ffi : Type} (st' : cml_state ffi) (env : sem_env) (ctMap_ : ctMap)
    (tenvS : tenv_store) (tids : Set type_ident) (tenv tenv' : type_env)
    (r : result sem_env v) : Prop :=
  ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
    weakCT ctMap' ctMap_ ∧
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
    store_type_extension tenvS tenvS' ∧
    match r with
    | .Rval env' =>
      type_all_env ctMap' tenvS' env' tenv' ∧
      type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
    | .Rerr (.Rraise err_v) =>
      type_v 0 ctMap' tenvS' err_v Texn ∧
      type_sound_invariant st' env ctMap' tenvS' ∅ tenv
    | .Rerr (.Rabort .Rtype_error) => False
    | .Rerr (.Rabort .Rtimeout_error) => True
    | .Rerr (.Rabort (.Rffi_error _)) => True

def DecsSound {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec) : Prop :=
  ∀ (st' : cml_state ffi) (r : result sem_env v) (ctMap_ : ctMap) (tenvS : tenv_store)
    (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
    evaluate_decs st env ds = (st', r) → type_ds false tenv ds tids tenv' →
    type_sound_invariant st env ctMap_ tenvS tids tenv →
    DecResult st' env ctMap_ tenvS tids tenv tenv' r

def empty_tenv : type_env := { v := nsEmpty, c := nsEmpty, t := nsEmpty }

theorem extend_dec_tenv_empty_left (t : type_env) : extend_dec_tenv empty_tenv t = t := by
  obtain ⟨a, b, c⟩ := t
  simp [extend_dec_tenv, empty_tenv, (nsAppend_nsEmpty _).2]

theorem extend_dec_env_empty_left (env : sem_env) :
    extend_dec_env (sem_env.mk nsEmpty nsEmpty) env = env := by
  cases env
  simp [extend_dec_env, sem_env.v_, sem_env.c, (nsAppend_nsEmpty _).2]

theorem set_union_empty {α : Type} (s : Set α) : s ∪ ∅ = s := by
  funext x; apply propext
  show (s x ∨ False) ↔ s x
  simp

theorem invariant_mono_tids {ffi : Type} {st : cml_state ffi} {env : sem_env} {c : ctMap}
    {S : tenv_store} {tids tids' : Set type_ident} {tenv : type_env} (hsub : tids' ⊆ tids)
    (h : type_sound_invariant st env c S tids tenv) : type_sound_invariant st env c S tids' tenv := by
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, h5⟩ := h
  exact ⟨h1, h2, ⟨fun x hx => h3 x ⟨hsub x hx.1, hx.2⟩, h3'⟩, h4, h5⟩

theorem empty_subset_set {α : Type} (s : Set α) : (∅ : Set α) ⊆ s := fun _ h => h.elim

theorem DecResult_mono_tids {ffi : Type} {st' : cml_state ffi} {env : sem_env} {c : ctMap}
    {S : tenv_store} {tids tids' : Set type_ident} {tenv tenv' : type_env} {r : result sem_env v}
    (hsub : tids ⊆ tids') (h : DecResult st' env c S tids tenv tenv' r) :
    DecResult st' env c S tids' tenv tenv' r := by
  obtain ⟨c', S', h1, h2, h3, h4⟩ := h
  exact ⟨c', S', h1, fun x hx => hsub x (h2 x hx), h3, h4⟩

theorem type_ds_single {tenv : type_env} {d : dec} {tids : Set type_ident} {tenv' : type_env}
    (h : type_ds false tenv [d] tids tenv') :
    ∃ decls1 tenv1, type_d false tenv d decls1 tenv1 ∧ tids = decls1 ∪ ∅ ∧
      tenv' = extend_dec_tenv empty_tenv tenv1 := by
  cases h with
  | cons _ _ _ _ decls1 tenv1 decls2 tenv2 hd hds hdis =>
    cases hds
    exact ⟨decls1, tenv1, hd, rfl, rfl⟩

theorem dec_single_reduce {ffi : Type} {st st' : cml_state ffi} {env : sem_env} {c : ctMap}
    {S : tenv_store} {tids : Set type_ident} {tenv tenv' : type_env} {d : dec} {r : result sem_env v}
    (h : type_ds false tenv [d] tids tenv') (inv : type_sound_invariant st env c S tids tenv)
    (k : ∀ decls1 tenv1, type_d false tenv d decls1 tenv1 →
      type_sound_invariant st env c S decls1 tenv → DecResult st' env c S decls1 tenv tenv1 r) :
    DecResult st' env c S tids tenv tenv' r := by
  obtain ⟨decls1, tenv1, hd, rfl, rfl⟩ := type_ds_single h
  rw [extend_dec_tenv_empty_left, set_union_empty]
  rw [set_union_empty] at inv
  exact k _ _ hd inv

theorem decs_type_sound_aux {ffi : Type} :
    (∀ (_ : cml_state ffi) (_ : sem_env) (_ : List exp), True) ∧
    (∀ (s : cml_state ffi) env ds, DecsSound s env ds) ∧
    (∀ (_ : cml_state ffi) (_ : sem_env) (_ : v) (_ : List (pat × exp)) (_ : v), True) := by
  apply evaluate.mutual_induct (motive1 := fun _ _ _ => True)
    (motive2 := fun s env ds => DecsSound s env ds)
    (motive3 := fun _ _ _ _ _ => True)
  all_goals (try (intros; exact trivial))
  all_goals sorry
