/-
  Translation of typeSoundScript.sml (part 2)
  Expression evaluation soundness, proved by induction on the evaluator.
-/
import LeanTypeSound.TypeSoundCore
open HOL4

/-- Typing of the result of evaluating a list of expressions. -/
def exp_res_ok (ctMap_ : ctMap) (tenvS : tenv_store) (tvs : Nat) (ts : List sem_t) :
    result (List v) v → Prop
  | .Rval vs => LIST_REL (type_v tvs ctMap_ tenvS) vs ts
  | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS val_ Texn
  | .Rerr (.Rabort .Rtimeout_error) => True
  | .Rerr (.Rabort (.Rffi_error _)) => True
  | .Rerr (.Rabort .Rtype_error) => False

/-- Typing of the result of evaluating a pattern match. -/
def match_res_ok (ctMap_ : ctMap) (tenvS : tenv_store) (tvs : Nat) (t : sem_t) :
    result (List v) v → Prop
  | .Rval vs => type_v tvs ctMap_ tenvS vs.head! t
  | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS val_ Texn
  | .Rerr (.Rabort .Rtimeout_error) => True
  | .Rerr (.Rabort (.Rffi_error _)) => True
  | .Rerr (.Rabort .Rtype_error) => False

def EvalSound {ffi : Type} (ctMap_ : ctMap) (s : cml_state ffi) (env : sem_env) (es : List exp) :
    Prop :=
  ∀ (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
    (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
    evaluate s env es = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE → good_ctMap ctMap_ →
    num_tvs tenvE = 0 →
    type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
    type_s ctMap_ s.refs tenvS → (tvs ≠ 0 → EVERY is_value es) →
    type_es tenv (bind_tvar tvs tenvE) es ts →
    ∃ (tenvS' : tenv_store), type_s ctMap_ s'.refs tenvS' ∧ store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧ s'.next_exn_stamp = s.next_exn_stamp ∧
      exp_res_ok ctMap_ tenvS' tvs ts r

def MatchSound {ffi : Type} (ctMap_ : ctMap) (s : cml_state ffi) (env : sem_env) (val_ : v)
    (pes : List (pat × exp)) (err_v : v) : Prop :=
  ∀ (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
    (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
    evaluate_match s env val_ pes err_v = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE →
    good_ctMap ctMap_ → num_tvs tenvE = 0 →
    type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
    type_s ctMap_ s.refs tenvS → type_v tvs ctMap_ tenvS val_ t1 →
    type_v 0 ctMap_ tenvS err_v Texn → type_pes tvs tvs tenv tenvE pes t1 t2 →
    ∃ (tenvS' : tenv_store), type_s ctMap_ s'.refs tenvS' ∧ store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧ s'.next_exn_stamp = s.next_exn_stamp ∧
      match_res_ok ctMap_ tenvS' tvs t2 r

theorem type_es_single {tenv : type_env} {tenvE : tenv_val_exp} {e : exp} {ts : List sem_t}
    (h : type_es tenv tenvE [e] ts) : ∃ t, ts = [t] ∧ type_e tenv tenvE e t := by
  cases h
  rename_i t ts h1 h2
  cases h2
  exact ⟨t, rfl, h1⟩

theorem tvs_zero_of_not_value {tvs : Nat} {es : List exp} (h : tvs ≠ 0 → EVERY is_value es = true)
    (hn : EVERY is_value es = false) : tvs = 0 := by
  cases tvs with
  | zero => rfl
  | succ n => rw [h (by simp)] at hn; cases hn

theorem exp_res_ok_err {c : ctMap} {S : tenv_store} {tvs tvs' : Nat} {ts ts' : List sem_t}
    {e : error_result v} (h : exp_res_ok c S tvs ts (.Rerr e)) : exp_res_ok c S tvs' ts' (.Rerr e) := by
  rcases e with _ | (_ | _ | _) <;> exact h

theorem fix_clock_eval_eq {ffi : Type} {st st' : cml_state ffi} {env : sem_env} {es : List exp}
    {r : result (List v) v} (h : fix_clock st (evaluate st env es) = (st', r)) :
    evaluate st env es = (st', r) := by
  rw [(fix_clock_evaluate st env es []).1] at h; exact h

theorem bind_tvar_zero (tenvE : tenv_val_exp) : bind_tvar 0 tenvE = tenvE := by
  simp [bind_tvar]

theorem type_all_env_ext {c : ctMap} {S S' : tenv_store} {env : sem_env} {tenv : type_env}
    (h : type_all_env c S env tenv) (hext : store_type_extension S S') : type_all_env c S' env tenv :=
  type_all_env_weakening _ _ _ _ _ _ ⟨weakCT_refl _, store_type_extension_weakS _ _ hext, h⟩

theorem type_v_ext {tvs : Nat} {c : ctMap} {S S' : tenv_store} {x : v} {t : sem_t}
    (h : type_v tvs c S x t) (hext : store_type_extension S S') : type_v tvs c S' x t :=
  type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inr rfl, weakCT_refl _, store_type_extension_weakS _ _ hext⟩

theorem LIST_REL_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ {xs : List α} {ys : List β}, LIST_REL R xs ys → LIST_REL R' xs ys
  | _, _, .nil => .nil
  | _, _, .cons _ _ _ _ h1 h2 => .cons _ _ _ _ (hR _ _ h1) (LIST_REL_mono hR h2)

theorem exp_res_ok_ext {c : ctMap} {S S' : tenv_store} {tvs : Nat} {ts : List sem_t}
    {r : result (List v) v} (h : exp_res_ok c S tvs ts r) (hext : store_type_extension S S') :
    exp_res_ok c S' tvs ts r := by
  rcases r with vs | (x | (_ | _ | _))
  · exact LIST_REL_mono (fun _ _ hx => type_v_ext hx hext) h
  · exact type_v_ext h hext
  all_goals exact h

theorem match_res_to_exp {ffi : Type} {c : ctMap} {S : tenv_store} {tvs : Nat} {t : sem_t}
    {st st' : cml_state ffi} {env : sem_env} {val_ err_v : v} {pes : List (pat × exp)}
    {r : result (List v) v} (hev : evaluate_match st env val_ pes err_v = (st', r))
    (h : match_res_ok c S tvs t r) : exp_res_ok c S tvs [t] r := by
  rcases r with vs | (x | (_ | _ | _))
  · have hl := evaluate_length.2.1 _ _ _ _ _ _ _ hev
    match vs, hl with
    | [w], _ => exact .cons _ _ _ _ h .nil
  all_goals exact h

theorem can_pmatch_all_of_typed {envC : env_ctor} {st : store v} {c : ctMap} {S : tenv_store}
    {tenv : type_env} {tvs : Nat} {val_ : v} {t : sem_t} (hok : ctMap_ok c)
    (hc : nsAll2 (type_ctor c) envC tenv.c) (hs : type_s c st S) (hv : type_v tvs c S val_ t) :
    ∀ (ps : List pat), (∀ p, p ∈ ps → ∃ b, type_p tvs tenv p t b) →
      can_pmatch_all envC st ps val_ = true := by
  intro ps hps
  rw [can_pmatch_all_EVERY]
  intro p hp
  obtain ⟨b, hb⟩ := hps p hp
  rcases pat_type_sound_p (cenv := envC) (st := st) hok hs hb hc val_ [] [] hv .nil with h | ⟨b', h, -⟩
  · rw [h]; simp
  · rw [h]; simp

theorem EvalSound.single {ffi : Type} {c : ctMap} {st s1 : cml_state ffi} {env : sem_env} {e : exp}
    {r1 : result (List v) v} {tenv : type_env} {tenvE : tenv_val_exp} {tenvS : tenv_store}
    {t : sem_t} (ih : EvalSound c st env [e]) (hev : evaluate st env [e] = (s1, r1))
    (htok : tenv_ok tenv) (hEok : tenv_val_exp_ok tenvE) (hg : good_ctMap c) (h0 : num_tvs tenvE = 0)
    (henv : type_all_env c tenvS env { tenv with v := add_tenvE tenvE tenv.v })
    (hs : type_s c st.refs tenvS) (hte : type_e tenv tenvE e t) :
    ∃ (S1 : tenv_store), type_s c s1.refs S1 ∧ store_type_extension tenvS S1 ∧
      s1.next_type_stamp = st.next_type_stamp ∧ s1.next_exn_stamp = st.next_exn_stamp ∧
      exp_res_ok c S1 0 [t] r1 :=
  ih r1 s1 tenv tenvE [t] 0 tenvS hev htok hEok hg h0 henv hs (by simp)
    (.cons _ _ _ _ _ _ (by rw [bind_tvar_zero]; exact hte) (.nil _ _))

theorem exp_res_single {c : ctMap} {S : tenv_store} {tvs : Nat} {t : sem_t} {vs : List v}
    (h : exp_res_ok c S tvs [t] (.Rval vs)) : ∃ w, vs = [w] ∧ type_v tvs c S w t := by
  cases h with
  | cons w _ _ _ hw hn => cases hn; exact ⟨w, rfl, hw⟩

theorem type_es_reverse {tenv : type_env} {E : tenv_val_exp} {es : List exp} {ts : List sem_t}
    (h : type_es tenv E es ts) : type_es tenv E es.reverse ts.reverse := by
  rw [type_es_list_rel] at h ⊢; exact LIST_REL_reverse h

theorem hval_con {tvs : Nat} {cn : Option (cml_id modN conN)} {es : List exp}
    (h : tvs ≠ 0 → EVERY is_value [exp.Con cn es] = true) : tvs ≠ 0 → EVERY is_value es.reverse = true := by
  intro hn; have := h hn; simp [EVERY] at this ⊢; exact this

theorem num_tvs_bind_tvar_of_zero {tvs : Nat} {tenvE : tenv_val_exp} (h0 : num_tvs tenvE = 0) :
    num_tvs (bind_tvar tvs tenvE) = tvs := by
  unfold bind_tvar; split <;> simp_all [num_tvs]

theorem type_v_closure_of_env {c : ctMap} {S : tenv_store} {tvs : Nat} {tenv : type_env}
    {tenvE : tenv_val_exp} {env : sem_env} {n : varN} {e : exp} {t1 t2 : sem_t}
    (htok : tenv_ok tenv) (hEok : tenv_val_exp_ok tenvE) (h0 : num_tvs tenvE = 0)
    (henv : type_all_env c S env { tenv with v := add_tenvE tenvE tenv.v })
    (ht1 : check_freevars tvs [] t1)
    (he : type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2) :
    type_v tvs c S (.Closure env n e) (Tfn t1 t2) := by
  obtain ⟨hc, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩⟩ := henv
  refine .closure _ _ _ tenv tenvE env n e t1 t2 htok hEok h0 hc ?_ hA2 hB2 ?_ ht1 he
  · intro id_
    constructor
    · intro hn
      cases hp : nsLookup (add_tenvE tenvE tenv.v) id_ with
      | none => rfl
      | some p => obtain ⟨w, hw, -⟩ := hB1 id_ p hp; cases hw.symm.trans hn
    · intro hn
      cases hp : nsLookup (sem_env_v env) id_ with
      | none => rfl
      | some w => obtain ⟨p, hp', -⟩ := hA1 id_ w hp; rw [hn] at hp'; cases hp'
  · intro id_ w p hw hp
    obtain ⟨p', hp', hr⟩ := hA1 id_ w hw
    rw [hp] at hp'; cases hp'; exact hr

theorem type_op_not_force {o : op} {ts : List sem_t} {t : sem_t} (h1 : getOpClass o = .Force)
    (h2 : type_op o ts t) : False := by
  cases o <;> simp [getOpClass] at h1
  case ThunkOp th =>
    cases th <;> simp at h1
    simp [type_op] at h2
theorem type_op_not_eval {o : op} {ts : List sem_t} {t : sem_t} (h1 : getOpClass o = .EvalOp)
    (h2 : type_op o ts t) : False := by
  cases o <;> simp [getOpClass] at h1
  case ThunkOp th => split at h1 <;> cases h1
  case Eval => simp [type_op] at h2
theorem opapp_of_funapp {o : op} (h1 : getOpClass o = .FunApp) : o = .Opapp := by
  cases o <;> simp [getOpClass] at h1 ⊢
  split at h1 <;> cases h1
theorem not_opapp_of_simple {o : op} (h1 : getOpClass o = .Simple) : o ≠ .Opapp := by
  rintro rfl; simp [getOpClass] at h1

theorem app_pre {ffi : Type} {c : ctMap} {st st1 : cml_state ffi} {env : sem_env} {es : List exp}
    {r1 : result (List v) v} {tenv : type_env} {tenvE : tenv_val_exp} {tenvS : tenv_store}
    {ts' : List sem_t} (ih : EvalSound c st env es.reverse)
    (hev1 : fix_clock st (evaluate st env es.reverse) = (st1, r1))
    (htok : tenv_ok tenv) (hEok : tenv_val_exp_ok tenvE) (hg : good_ctMap c) (h0 : num_tvs tenvE = 0)
    (henv : type_all_env c tenvS env { tenv with v := add_tenvE tenvE tenv.v })
    (hs : type_s c st.refs tenvS) (hes : type_es tenv tenvE es ts') :
    ∃ (S1 : tenv_store), type_s c st1.refs S1 ∧ store_type_extension tenvS S1 ∧
      st1.next_type_stamp = st.next_type_stamp ∧ st1.next_exn_stamp = st.next_exn_stamp ∧
      exp_res_ok c S1 0 ts'.reverse r1 :=
  ih r1 st1 tenv tenvE ts'.reverse 0 tenvS (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs (by simp)
    (by rw [bind_tvar_zero]; exact type_es_reverse hes)

theorem exp_res_ok_list_result {c : ctMap} {S : tenv_store} {t : sem_t} {r : result v v}
    (h : match r with
      | .Rval val_ => type_v 0 c S val_ t
      | .Rerr (.Rraise val_) => type_v 0 c S val_ Texn
      | .Rerr (.Rabort (.Rffi_error _)) => True
      | .Rerr (.Rabort _) => False) : exp_res_ok c S 0 [t] (list_result r) := by
  rcases r with w | (x | (_ | _ | _))
  · exact .cons _ _ _ _ h .nil
  all_goals first | exact h | trivial | exact h.elim

theorem do_log_bool_ne_none (l : lop) (b : Bool) (e : exp) : do_log l (Boolv b) e ≠ none := by
  cases l <;> cases b <;> simp [do_log, Boolv, v_beq_eq, v_beq, v_list_beq]
theorem do_if_bool_ne_none (b : Bool) (e1 e2 : exp) : do_if (Boolv b) e1 e2 ≠ none := by
  cases b <;> simp [do_if, Boolv, v_beq_eq, v_beq, v_list_beq]
theorem do_log_val_eq {l : lop} {w w' : v} {e : exp} (h : do_log l w e = some (.Val w')) : w' = w := by
  unfold do_log at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, exp_or_val.Val.injEq] at h; exact h.symm
    · cases h

theorem EvalSound.single_val {ffi : Type} {c : ctMap} {st s1 : cml_state ffi} {env : sem_env} {e : exp}
    {vs : List v} {tenv : type_env} {tenvE : tenv_val_exp} {tenvS : tenv_store}
    {t : sem_t} (ih : EvalSound c st env [e]) (hev : evaluate st env [e] = (s1, .Rval vs))
    (htok : tenv_ok tenv) (hEok : tenv_val_exp_ok tenvE) (hg : good_ctMap c) (h0 : num_tvs tenvE = 0)
    (henv : type_all_env c tenvS env { tenv with v := add_tenvE tenvE tenv.v })
    (hs : type_s c st.refs tenvS) (hte : type_e tenv tenvE e t) :
    ∃ (S1 : tenv_store) (w : v), vs = [w] ∧ type_s c s1.refs S1 ∧ store_type_extension tenvS S1 ∧
      s1.next_type_stamp = st.next_type_stamp ∧ s1.next_exn_stamp = st.next_exn_stamp ∧
      type_v 0 c S1 w t := by
  obtain ⟨S1, hs1, hext, hn1, hn2, hres⟩ := EvalSound.single ih hev htok hEok hg h0 henv hs hte
  obtain ⟨w, rfl, hw⟩ := exp_res_single hres
  exact ⟨S1, w, rfl, hs1, hext, hn1, hn2, hw⟩

theorem type_all_env_opt_bind {c : ctMap} {S : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp} {xo : Option varN} {w : v} {t1 : sem_t}
    (henv : type_all_env c S env { tenv with v := add_tenvE tenvE tenv.v })
    (hw : type_v 0 c S w t1) :
    type_all_env c S (sem_env.mk (nsOptBind xo w env.v_) env.c)
      { tenv with v := add_tenvE (opt_bind_name xo 0 t1 tenvE) tenv.v } := by
  cases xo with
  | none => exact henv
  | some x => exact ⟨henv.1, nsAll2_nsBind _ _ _ _ _ _ ⟨hw, henv.2⟩⟩

theorem LIST_REL_map_right {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, LIST_REL (fun a b => R a (f b)) xs ys → LIST_REL R xs (ys.map f)
  | _, _, .nil => .nil
  | _, _, .cons _ _ _ _ h1 h2 => .cons _ _ _ _ h1 (LIST_REL_map_right h2)

theorem LIST_REL_map_right_inv {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, LIST_REL R xs (ys.map f) → LIST_REL (fun a b => R a (f b)) xs ys
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons _ _ _ _ h1 h2 => .cons _ _ _ _ h1 (LIST_REL_map_right_inv h2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem type_all_env_bindList {c : ctMap} {S : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp} {tvs : Nat} {l : List (varN × v)} {bindings : List (varN × sem_t)}
    (henv : type_all_env c S env { tenv with v := add_tenvE tenvE tenv.v })
    (hl : LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
      p1.1 = p2.1 ∧ type_v tvs c S p1.2 p2.2) l bindings) :
    type_all_env c S (sem_env.mk (nsBindList l env.v_) env.c)
      { tenv with v := add_tenvE (bind_var_list tvs bindings tenvE) tenv.v } := by
  refine ⟨henv.1, ?_⟩
  show nsAll2 _ (nsBindList l env.v_) (add_tenvE (bind_var_list tvs bindings tenvE) tenv.v)
  rw [add_tenvE_bvl]
  refine nsAll2_nsBindList _ _ _ _ _ ⟨LIST_REL_map_right (LIST_REL_mono ?_ hl), henv.2⟩
  rintro ⟨x, w⟩ ⟨y, t⟩ ⟨h1, h2⟩
  exact ⟨h1, h2⟩

set_option hygiene false in
macro "ev_split" : tactic => `(tactic| (
  split at hev <;>
  (rename_i heq; rw [hev1] at heq; simp only [Prod.mk.injEq, result.Rval.injEq, result.Rerr.injEq,
     error_result.Rraise.injEq, error_result.Rabort.injEq, reduceCtorEq, false_and, and_false] at heq)))

theorem exp_type_sound_aux {ffi : Type} (ctMap_ : ctMap) :
    (∀ (s : cml_state ffi) env es, EvalSound ctMap_ s env es) ∧
    (∀ (_ : cml_state ffi) (_ : sem_env) (_ : List dec), True) ∧
    (∀ (s : cml_state ffi) env val_ pes err_v, MatchSound ctMap_ s env val_ pes err_v) := by
  apply evaluate.mutual_induct (motive1 := fun s env es => EvalSound ctMap_ s env es)
    (motive2 := fun _ _ _ => True)
    (motive3 := fun s env val_ pes err_v => MatchSound ctMap_ s env val_ pes err_v)
  all_goals (try (intros; exact trivial))
  case case3 =>
    intro st env e st1 vs hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [hev1, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte
    rename_i he hfv
    obtain ⟨S1, hs1, hext, hn1, hn2, hres⟩ := ih _ _ tenv tenvE [Texn] 0 tenvS hev1 htok hEok hg h0
      henv hs (by simp) (.cons _ _ _ _ _ _ (by rw [bind_tvar_zero]; exact he) (.nil _ _))
    refine ⟨S1, hs1, hext, hn1, hn2, ?_⟩
    cases hres
    rename_i hw hnil
    cases hnil
    exact hw
  case case4 =>
    intro st env e st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [hev1, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte
    rename_i he hfv
    obtain ⟨S1, hs1, hext, hn1, hn2, hres⟩ := ih _ _ tenv tenvE [Texn] 0 tenvS hev1 htok hEok hg h0
      henv hs (by simp) (.cons _ _ _ _ _ _ (by rw [bind_tvar_zero]; exact he) (.nil _ _))
    exact ⟨S1, hs1, hext, hn1, hn2, exp_res_ok_err hres⟩
  case case1 =>
    intro st env r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    cases hty
    exact ⟨tenvS, hs, store_type_extension_refl _, rfl, rfl, .nil⟩
  case case2 =>
    intro st env l r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    refine ⟨tenvS, hs, store_type_extension_refl _, rfl, rfl, .cons _ _ _ _ ?_ .nil⟩
    cases hte <;> constructor
  case case5 =>
    intro st env e pes st1 vs hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | handle _ _ _ _ bof he hne hdist hpt hbt =>
    exact EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
  case case6 =>
    intro st env e pes st1 val_ hev1 hcan ih ihm r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    rw [if_pos (by simpa [List.attach_map_val] using hcan)] at hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | handle _ _ _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    have hv : type_v 0 ctMap_ S1 val_ Texn := hres
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := ihm r s' tenv tenvE Texn t 0 S1 hev htok hEok hg h0
      (type_all_env_ext henv hext1) hs1 hv hv
      (fun pe hpe => ⟨bof pe, hdist pe hpe, by rw [← h0]; exact hpt pe hpe, hbt pe hpe⟩)
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2,
      match_res_to_exp hev hres2⟩
  case case7 =>
    intro st env e pes st1 val_ hev1 hcan ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | handle _ _ _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    have hv : type_v 0 ctMap_ S1 val_ Texn := hres
    apply hcan
    have := can_pmatch_all_of_typed (envC := env.c) (tenv := tenv) hg.1 (type_all_env_ext henv hext1).1 hs1 hv
      (pes.map Prod.fst) (by
        intro p hp
        obtain ⟨pe, hpe, rfl⟩ := List.mem_map.1 hp
        exact ⟨bof pe, by rw [← h0]; exact hpt pe hpe⟩)
    simpa [List.attach_map_val] using this
  case case8 =>
    intro st env e pes st1 a hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | handle _ _ _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case9 =>
    intro st env cn es hcheck st1 vs hev1 hbuild ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    obtain ⟨w, hw⟩ := do_con_check_build_conv env.c cn vs.reverse _ hcheck
    rw [hw] at hbuild; cases hbuild
  case case10 =>
    intro st env cn es hcheck st1 vs hev1 w hbuild ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [hcheck, if_true, hev1, hbuild, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | con_some _ _ _ ts' tvs' ts tn hfv hlen hes hlook =>
      obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := ih (.Rval vs) st1 tenv tenvE _ tvs tenvS hev1 htok hEok
        hg h0 henv hs (hval_con hval) (type_es_reverse hes)
      obtain ⟨w', hw', htw⟩ := build_conv_type_sound env.c _ vs tvs ts ctMap_ S1 ts' tn tenv.c tvs' tenvE
        es.length ⟨henv.1, hcheck, h0, by simpa [EVERY] using hfv, hlen, hres, hlook⟩
      rw [hw'] at hbuild; cases hbuild
      exact ⟨S1, hs1, hext1, hn1, hn2, .cons _ _ _ _ htw .nil⟩
    | con_none _ _ ts hes =>
      obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := ih (.Rval vs) st1 tenv tenvE _ tvs tenvS hev1 htok hEok
        hg h0 henv hs (hval_con hval) (type_es_reverse hes)
      simp only [build_conv, Option.some.injEq] at hbuild
      subst hbuild
      have hres' := LIST_REL_reverse (show LIST_REL (type_v tvs ctMap_ S1) vs ts.reverse from hres)
      rw [List.reverse_reverse] at hres'
      exact ⟨S1, hs1, hext1, hn1, hn2, .cons _ _ _ _
        (.conv_none _ _ _ _ _ (LIST_REL_length hres') (LIST_REL_getElem_bang hres')) .nil⟩
  case case11 =>
    intro st env cn es hcheck st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [hcheck, if_true, hev1, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | con_some _ _ _ ts' tvs' ts tn hfv hlen hes hlook =>
      obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := ih (.Rerr err) st1 tenv tenvE _ tvs tenvS hev1 htok hEok
        hg h0 henv hs (hval_con hval) (type_es_reverse hes)
      exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
    | con_none _ _ ts hes =>
      obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := ih (.Rerr err) st1 tenv tenvE _ tvs tenvS hev1 htok hEok
        hg h0 henv hs (hval_con hval) (type_es_reverse hes)
      exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case12 =>
    intro st env cn es hcheck r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso; apply hcheck
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | con_some _ _ _ ts' tvs' ts tn hfv hlen hes hlook =>
      obtain ⟨_, stmp, h1, _⟩ := (type_env_conv_thm _ _ _ henv.1 _ tvs' ts tn tn).1 hlook
      have hl := type_es_length _ _ _ _ hes
      simp only [List.length_map] at hl
      simp [do_con_check, show nsLookup env.c _ = _ from h1, hl]
    | con_none _ _ ts hes => rfl
  case case13 =>
    intro st env n hlook r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | var _ _ tvs' t targs hlen hfv hl =>
      subst hlen
      obtain ⟨w, hw, -⟩ := lookup_var_sound n tvs tenvE targs t ctMap_ tenvS env tenv
        ⟨hl, hg.1, hEok, h0, by simpa [EVERY, num_tvs_bind_tvar_of_zero h0] using hfv, henv⟩
      rw [hlook] at hw; cases hw
  case case14 =>
    intro st env n w hlook r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [hlook, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | var _ _ tvs' t targs hlen hfv hl =>
      subst hlen
      obtain ⟨w', hw, htw⟩ := lookup_var_sound n tvs tenvE targs t ctMap_ tenvS env tenv
        ⟨hl, hg.1, hEok, h0, by simpa [EVERY, num_tvs_bind_tvar_of_zero h0] using hfv, henv⟩
      rw [hlook] at hw; cases hw
      exact ⟨tenvS, hs, store_type_extension_refl _, rfl, rfl, .cons _ _ _ _ htw .nil⟩
  case case15 =>
    intro st env x e r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | fun_ _ _ _ t1 t2 hfv he =>
      rw [num_tvs_bind_tvar_of_zero h0] at hfv
      exact ⟨tenvS, hs, store_type_extension_refl _, rfl, rfl,
        .cons _ _ _ _ (type_v_closure_of_env htok hEok h0 henv hfv he) .nil⟩
  case case16 =>
    intro st env o es st1 vs hev1 hcls env' e hop hclk ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hcls, hop] at hev
    rw [dif_pos hclk] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    exact ⟨S1, hs1, hext1, hn1, hn2, trivial⟩
  case case17 =>
    intro st env o es st1 vs hev1 hcls env' e hop hclk ih ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hcls, hop] at hev
    rw [dif_neg hclk] at hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    obtain rfl := opapp_of_funapp hcls
    have hres' := LIST_REL_reverse (show LIST_REL (type_v 0 ctMap_ S1) vs ts'.reverse from hres)
    rw [List.reverse_reverse] at hres'
    obtain ⟨env2, e2, tenv2, tenvE2, htok2, hEok2, h02, henv2, hte2, hop2⟩ :=
      opapp_type_sound ctMap_ S1 vs.reverse ts' t ⟨hg.1, hop', hres'⟩
    rw [hop] at hop2; cases hop2
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := EvalSound.single ih2 hev htok2 hEok2 hg h02 henv2 hs1 hte2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2, hres2⟩
  case case18 =>
    intro st env o es st1 vs hev1 hcls hop ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    obtain rfl := opapp_of_funapp hcls
    have hres' := LIST_REL_reverse (show LIST_REL (type_v 0 ctMap_ S1) vs ts'.reverse from hres)
    rw [List.reverse_reverse] at hres'
    obtain ⟨env2, e2, tenv2, tenvE2, htok2, hEok2, h02, henv2, hte2, hop2⟩ :=
      opapp_type_sound ctMap_ S1 vs.reverse ts' t ⟨hg.1, hop', hres'⟩
    rw [hop] at hop2; cases hop2
  case case19 | case20 | case21 | case22 | case23 | case24 | case25 | case26 =>
    intro st env o es st1 vs hev1 hcls
    intros
    intro r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | app _ _ _ ts' t hes hop' hfv => exact type_op_not_force hcls hop'
  case case27 | case28 | case29 | case30 | case31 | case32 =>
    intro st env o es st1 vs hev1 hcls
    intros
    intro r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | app _ _ _ ts' t hes hop' hfv => exact type_op_not_eval hcls hop'
  case case33 =>
    intro st env o es st1 vs hev1 hcls hdo ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    obtain ⟨S2, store2, ffi2, r2, -, -, hdo2, -⟩ := op_type_sound ctMap_ S1 vs o ts' t st1.refs st1.ffi
      ⟨hg, not_opapp_of_simple hcls, hs1, hop', by rw [h0] at hfv; exact hfv, hres⟩
    rw [hdo] at hdo2; cases hdo2
  case case34 =>
    intro st env o es st1 vs hev1 hcls refs ffi_ r0 hdo ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hcls, hdo, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    obtain ⟨S2, store2, ffi2, r2, hext2, hs2, hdo2, hr2⟩ := op_type_sound ctMap_ S1 vs o ts' t st1.refs st1.ffi
      ⟨hg, not_opapp_of_simple hcls, hs1, hop', by rw [h0] at hfv; exact hfv, hres⟩
    rw [hdo] at hdo2
    simp only [Option.some.injEq, Prod.mk.injEq] at hdo2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hdo2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn1, hn2,
      exp_res_ok_list_result hr2⟩
  case case35 =>
    intro st env o es st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | app _ _ _ ts' t hes hop' hfv =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ := app_pre ih hev1 htok hEok hg h0 henv hs hes
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case36 =>
    intro st env l e1 e2 st1 vs hev1 hlog ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | log _ _ _ _ he1 he2 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    obtain ⟨b, rfl⟩ := prim_canonical_Boolv_thm _ _ _ _ ⟨hw, hg.1, hg.2.1⟩
    exact do_log_bool_ne_none _ _ _ hlog
  case case37 =>
    intro st env l e1 e2 st1 vs hev1 e hlog ih ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    split at hev <;> (rename_i hx; rw [hlog] at hx; simp only [Option.some.injEq,
      exp_or_val.Exp.injEq, reduceCtorEq] at hx)
    subst hx
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | log _ _ _ _ he1 he2 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    obtain rfl := do_log_exp hlog
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := EvalSound.single ih2 hev htok hEok hg h0
      (type_all_env_ext henv hext1) hs1 he2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2, hres2⟩
  case case38 =>
    intro st env l e1 e2 st1 vs hev1 w' hlog ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    split at hev <;> (rename_i hx; rw [hlog] at hx; simp only [Option.some.injEq,
      exp_or_val.Val.injEq, reduceCtorEq] at hx)
    subst hx
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | log _ _ _ _ he1 he2 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    obtain rfl := do_log_val_eq hlog
    exact ⟨S1, hs1, hext1, hn1, hn2, .cons _ _ _ _ hw .nil⟩
  case case39 =>
    intro st env l e1 e2 st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | log _ _ _ _ he1 he2 =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case40 =>
    intro st env e1 e2 e3 st1 vs hev1 hif ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | if_ _ _ _ _ _ he1 he2 he3 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    obtain ⟨b, rfl⟩ := prim_canonical_Boolv_thm _ _ _ _ ⟨hw, hg.1, hg.2.1⟩
    exact do_if_bool_ne_none _ _ _ hif
  case case41 =>
    intro st env e1 e2 e3 st1 vs hev1 e hif ih ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    split at hev <;> (rename_i hx; rw [hif] at hx; simp only [Option.some.injEq,
      reduceCtorEq] at hx)
    subst hx
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | if_ _ _ _ _ _ he1 he2 he3 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    have hte' : type_e tenv tenvE e t := by
      rcases do_if_exp hif with rfl | rfl
      · exact he2
      · exact he3
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := EvalSound.single ih2 hev htok hEok hg h0
      (type_all_env_ext henv hext1) hs1 hte'
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2, hres2⟩
  case case42 =>
    intro st env e1 e2 e3 st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | if_ _ _ _ _ _ he1 he2 he3 =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case43 =>
    intro st env e pes st1 vs hev1 hcan ih ihm r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    rw [if_pos (by simpa [List.attach_map_val] using hcan)] at hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | mat _ _ t1 _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    have hbe : type_v 0 ctMap_ S1 bind_exn_v Texn := (type_v_exn 0 ctMap_ S1 hg.2.2.1).2.2.1
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := ihm r s' tenv tenvE t1 t 0 S1 hev htok hEok hg h0
      (type_all_env_ext henv hext1) hs1 hw hbe
      (fun pe hpe => ⟨bof pe, hdist pe hpe, by rw [← h0]; exact hpt pe hpe, hbt pe hpe⟩)
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2,
      match_res_to_exp hev hres2⟩
  case case44 =>
    intro st env e pes st1 vs hev1 hcan ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | mat _ _ t1 _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    apply hcan
    have := can_pmatch_all_of_typed (envC := env.c) (tenv := tenv) hg.1 (type_all_env_ext henv hext1).1 hs1 hw
      (pes.map Prod.fst) (by
        intro p hp
        obtain ⟨pe, hpe, rfl⟩ := List.mem_map.1 hp
        exact ⟨bof pe, by rw [← h0]; exact hpt pe hpe⟩)
    simpa [List.attach_map_val] using this
  case case45 =>
    intro st env e pes st1 err hev1 ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | mat _ _ t1 _ _ bof he hne hdist hpt hbt =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case50 =>
    intro st env e a ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | tannot _ _ _ hc1 hc2 he =>
    exact ih r s' tenv tenvE _ tvs tenvS hev htok hEok hg h0 henv hs
      (by simpa [EVERY, is_value] using hval) (.cons _ _ _ _ _ _ he (.nil _ _))
  case case51 =>
    intro st env e a ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    cases hte with
    | lannot _ _ _ _ he =>
    exact ih r s' tenv tenvE _ tvs tenvS hev htok hEok hg h0 henv hs
      (by simpa [EVERY, is_value] using hval) (.cons _ _ _ _ _ _ he (.nil _ _))
  case case52 =>
    intro st env e1 e2 es st1 vs hev1 st2 vs2 hev2 ih1 ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hev2, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    cases hty with
    | cons _ _ t1 _ ts2 he1 hes2 =>
    have hv1 : tvs ≠ 0 → EVERY is_value [e1] = true := fun h => by
      have := hval h; simp [EVERY] at this ⊢; exact this.1
    have hv2 : tvs ≠ 0 → EVERY is_value (e2 :: es) = true := fun h => by
      have := hval h; simp [EVERY] at this ⊢; exact this.2
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres1⟩ := ih1 _ _ tenv tenvE [t1] tvs tenvS (fix_clock_eval_eq hev1)
      htok hEok hg h0 henv hs hv1 (.cons _ _ _ _ _ _ he1 (.nil _ _))
    obtain ⟨w, rfl, hw⟩ := exp_res_single hres1
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := ih2 _ _ tenv tenvE ts2 tvs S1 hev2
      htok hEok hg h0 (type_all_env_ext henv hext1) hs1 hv2 hes2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2,
      .cons _ _ _ _ (type_v_ext hw hext2) hres2⟩
  case case53 =>
    intro st env e1 e2 es st1 vs hev1 st2 err hev2 ih1 ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hev2, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    cases hty with
    | cons _ _ t1 _ ts2 he1 hes2 =>
    have hv1 : tvs ≠ 0 → EVERY is_value [e1] = true := fun h => by
      have := hval h; simp [EVERY] at this ⊢; exact this.1
    have hv2 : tvs ≠ 0 → EVERY is_value (e2 :: es) = true := fun h => by
      have := hval h; simp [EVERY] at this ⊢; exact this.2
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres1⟩ := ih1 _ _ tenv tenvE [t1] tvs tenvS (fix_clock_eval_eq hev1)
      htok hEok hg h0 henv hs hv1 (.cons _ _ _ _ _ _ he1 (.nil _ _))
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := ih2 _ _ tenv tenvE ts2 tvs S1 hev2
      htok hEok hg h0 (type_all_env_ext henv hext1) hs1 hv2 hes2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2,
      exp_res_ok_err hres2⟩
  case case54 =>
    intro st env e1 e2 es st1 err hev1 ih1 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    cases hty with
    | cons _ _ t1 _ ts2 he1 hes2 =>
    have hv1 : tvs ≠ 0 → EVERY is_value [e1] = true := fun h => by
      have := hval h; simp [EVERY] at this ⊢; exact this.1
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres1⟩ := ih1 _ _ tenv tenvE [t1] tvs tenvS (fix_clock_eval_eq hev1)
      htok hEok hg h0 henv hs hv1 (.cons _ _ _ _ _ _ he1 (.nil _ _))
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres1⟩
  case case71 =>
    intro st env val_ err_v r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr hpes
    rw [evaluate_match.eq_def] at hev
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    exact ⟨tenvS, hs, store_type_extension_refl _, rfl, rfl, herr⟩
  case case72 =>
    intro st env val_ err_v p e pes hdist hpm ihm r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr hpes
    rw [evaluate_match.eq_def] at hev
    simp only [hdist, if_true, hpm] at hev
    exact ihm r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr
      (fun pe hpe => hpes pe (List.mem_cons_of_mem _ hpe))
  case case73 =>
    intro st env val_ err_v p e pes hdist hpm r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr hpes
    exfalso
    obtain ⟨bs, hd, hp, he⟩ := hpes (p, e) List.mem_cons_self
    rcases pat_type_sound_p (cenv := env.c) hg.1 hs hp henv.1 val_ [] [] hv .nil with h | ⟨b', h, -⟩ <;>
      rw [hpm] at h <;> cases h
  case case74 =>
    intro st env val_ err_v p e pes hdist env_v' hpm ih r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr hpes
    rw [evaluate_match.eq_def] at hev
    simp only [hdist, if_true, hpm] at hev
    obtain ⟨bs, hd, hp, he⟩ := hpes (p, e) List.mem_cons_self
    rcases pat_type_sound_p (cenv := env.c) hg.1 hs hp henv.1 val_ [] [] hv .nil with h | ⟨b', h, hrel⟩
    · rw [hpm] at h; cases h
    rw [hpm] at h; cases h
    rw [List.append_nil] at hrel
    have henv' := type_all_env_bindList henv hrel
    rw [← nsAppend_to_nsBindList] at henv'
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := ih r s' tenv (bind_var_list tvs bs tenvE) [t2] 0 tenvS hev
      htok (type_p_bvl.1 _ _ _ _ _ hp _ hEok) hg (by rw [num_tvs_bind_var_list]; exact h0) henv' hs
      (by simp) (.cons _ _ _ _ _ _ (by rw [bind_tvar_zero]; exact he) (.nil _ _))
    refine ⟨S2, hs2, hext2, hn3, hn4, ?_⟩
    rcases r with vs | (x | (_ | _ | _))
    · obtain ⟨w, rfl, hw⟩ := exp_res_single hres2
      exact type_v_weakening _ _ _ _ _ hw _ _ _ ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩
    all_goals exact hres2
  case case75 =>
    intro st env val_ err_v p e pes hdist r s' tenv tenvE t1 t2 tvs tenvS hev htok hEok hg h0 henv hs hv herr hpes
    exfalso
    obtain ⟨bs, hd, hp, he⟩ := hpes (p, e) List.mem_cons_self
    exact hdist hd
  case case46 =>
    intro st env xo e1 e2 st1 vs hev1 ih1 ih2 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | let_ _ _ _ t1 _ _ he1 he2 =>
    obtain ⟨S1, w, rfl, hs1, hext1, hn1, hn2, hw⟩ :=
      EvalSound.single_val ih1 (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    have hfv := type_v_freevars _ _ _ _ _ hw
    have hEok' : tenv_val_exp_ok (opt_bind_name xo 0 t1 tenvE) := by
      cases xo with
      | none => exact hEok
      | some x => exact ⟨by simpa [h0] using hfv, hEok⟩
    have h0' : num_tvs (opt_bind_name xo 0 t1 tenvE) = 0 := by
      cases xo <;> simpa [opt_bind_name, num_tvs] using h0
    obtain ⟨S2, hs2, hext2, hn3, hn4, hres2⟩ := EvalSound.single ih2 hev htok hEok' hg h0'
      (type_all_env_opt_bind (type_all_env_ext henv hext1) hw) hs1 he2
    exact ⟨S2, hs2, store_type_extension_trans _ _ _ ⟨hext1, hext2⟩, hn3.trans hn1, hn4.trans hn2, hres2⟩
  case case47 =>
    intro st env xo e1 e2 st1 err hev1 ih1 r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    rw [evaluate.eq_def] at hev
    simp only at hev
    ev_split
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | let_ _ _ _ t1 _ _ he1 he2 =>
    obtain ⟨S1, hs1, hext1, hn1, hn2, hres⟩ :=
      EvalSound.single ih1 (fix_clock_eval_eq hev1) htok hEok hg h0 henv hs he1
    exact ⟨S1, hs1, hext1, hn1, hn2, exp_res_ok_err hres⟩
  case case48 =>
    intro st env funs e hdist ih r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | letrec _ _ bindings _ _ hfuns he =>
    have hd : ALL_DISTINCT (funs.map Prod.fst) := by
      have := type_funs_distinct _ _ _ _ hfuns
      simpa using this
    rw [evaluate.eq_def] at hev
    simp only at hev
    rw [if_pos hd] at hev
    have hrel := type_recfun_env funs ctMap_ tenvS 0 tenv tenvE env bindings
      ⟨htok, henv, hEok, h0, by rw [bind_tvar_zero]; exact hfuns, hd⟩
    have henv' := type_all_env_bindList (tvs := 0) (bindings := bindings) henv
      (LIST_REL_mono (fun _ _ h => h) (LIST_REL_map_right_inv hrel))
    rw [← build_rec_env_nsBindList] at henv'
    exact EvalSound.single ih hev htok (tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v tenvE
      ⟨hfuns, hEok⟩) hg (by rw [num_tvs_bind_var_list]; exact h0) henv' hs he
  case case49 =>
    intro st env funs e hdist r s' tenv tenvE ts tvs tenvS hev htok hEok hg h0 henv hs hval hty
    exfalso
    obtain rfl := tvs_zero_of_not_value hval (by simp [EVERY, is_value])
    obtain ⟨t, rfl, hte⟩ := type_es_single hty
    rw [bind_tvar_zero] at hte
    cases hte with
    | letrec _ _ bindings _ _ hfuns he =>
    apply hdist
    have := type_funs_distinct _ _ _ _ hfuns
    simpa [List.attach_map_val] using this
