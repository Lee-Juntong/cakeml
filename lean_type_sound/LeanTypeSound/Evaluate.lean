/-
  Translation of evaluateScript.sml
  Functional big-step semantics for evaluation of CakeML programs.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Tactics
import LeanTypeSound.FpSem
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.Ffi
import LeanTypeSound.SemanticPrimitives

open HOL4

/- HOL4:
Definition fix_clock_def:
  fix_clock s (s',res) =
    (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End
-/
def fix_clock {ffi α : Type} (s : cml_state ffi) (p : cml_state ffi × α) :
    cml_state ffi × α :=
  let (s', res) := p
  ({ s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock }, res)

/- HOL4:
Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End
-/
def dec_clock {ffi : Type} (s : cml_state ffi) : cml_state ffi :=
  { s with clock := s.clock - 1 }

/- HOL4:
Definition do_eval_res_def:
  do_eval_res vs s =
    case do_eval vs s.eval_state of
    | NONE => (s,Rerr (Rabort Rtype_error))
    | SOME (env1,decs,es1) => (s with eval_state := es1,Rval (env1,decs))
End
-/
def do_eval_res {ffi : Type} (vs : List v) (s : cml_state ffi) :
    cml_state ffi × result (sem_env × List dec) v :=
  match do_eval vs s.eval_state_field with
  | none => (s, .Rerr (.Rabort .Rtype_error))
  | some (env1, decs, es1) => ({ s with eval_state_field := es1 }, .Rval (env1, decs))

/- HOL4:
Definition list_result_def[simp]:
  list_result (Rval v) = Rval [v] ∧
  list_result (Rerr e) = Rerr e
End
-/
def list_result {α β : Type} : result α β → result (List α) β
  | .Rval v => .Rval [v]
  | .Rerr e => .Rerr e

/- HOL4:
Definition evaluate_def[nocompute]:
  evaluate st env [] = (st, Rval [])
  ∧ ...
  ∧ evaluate_match st env v [] err_v = (st, Rerr (Rraise err_v))
  ∧ ...
  ∧ evaluate_decs st env [] = (st, Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧ ...
End

  evaluate, evaluate_match, and evaluate_decs are mutually recursive
  with complex termination (clock-based). We use mutual partial def.
-/
-- Auxiliary lemmas used to prove termination of the evaluator.
theorem fix_clock_clock_le {ffi α : Type} {s s' : cml_state ffi} {p : cml_state ffi × α} {r : α}
    (h : fix_clock s p = (s', r)) : s'.clock ≤ s.clock := by
  obtain ⟨a, b⟩ := p
  simp only [fix_clock, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only; split <;> omega

theorem lex_le_lt {a a' b b' : Nat} (h1 : a' ≤ a) (h2 : b' < b) :
    Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ h2

theorem lex_lt {a a' b b' : Nat} (h : a' < a) :
    Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2) (a', b') (a, b) :=
  Prod.Lex.left _ _ h

theorem do_log_exp {l : lop} {val_ : v} {e e' : exp}
    (h : do_log l val_ e = some (.Exp e')) : e' = e := by
  unfold do_log at h
  split at h
  · simp only [Option.some.injEq, exp_or_val.Exp.injEq] at h; exact h.symm
  · split at h <;> simp at h

theorem do_if_exp {val_ : v} {e1 e2 e : exp} (h : do_if val_ e1 e2 = some e) : e = e1 ∨ e = e2 := by
  unfold do_if at h
  split at h
  · simp only [Option.some.injEq] at h; exact Or.inl h.symm
  · split at h
    · simp only [Option.some.injEq] at h; exact Or.inr h.symm
    · simp at h

theorem list_sizeOf_append {α : Type} [SizeOf α] (l1 l2 : List α) :
    sizeOf (l1 ++ l2) + 1 = sizeOf l1 + sizeOf l2 := by
  induction l1 with
  | nil => simp; omega
  | cons a l ih => simp; omega

theorem list_sizeOf_reverse {α : Type} [SizeOf α] (l : List α) : sizeOf l.reverse = sizeOf l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have := list_sizeOf_append l.reverse [a]
    simp at this ⊢; omega

theorem pat_sizeOf_pos (p : pat) : 0 < sizeOf p := by
  cases p <;> simp <;> omega

theorem list_sizeOf_pos {α : Type} [SizeOf α] (l : List α) : 0 < sizeOf l := by
  cases l <;> simp <;> omega

mutual
def evaluate {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (es : List exp) : cml_state ffi × result (List v) v :=
  match es with
  | [] => (st, .Rval [])
  | [.Lit l] => (st, .Rval [.Litv l])
  | [.Raise e] =>
    match evaluate st env [e] with
    | (st', .Rval vs) => (st', .Rerr (.Rraise vs.head!))
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Handle e pes] =>
    match _hfc : fix_clock st (evaluate st env [e]) with
    | (st', .Rval v') => (st', .Rval v')
    | (st', .Rerr (.Rraise val_)) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) val_ then
        evaluate_match st' env val_ pes val_
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr (.Rabort a)) => (st', .Rerr (.Rabort a))
  | [.Con cn es'] =>
    if do_con_check env.c cn es'.length then
      match evaluate st env es'.reverse with
      | (st', .Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some v' => (st', .Rval [v'])
      | (st', .Rerr e) => (st', .Rerr e)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Var n] =>
    match nsLookup env.v_ n with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some v' => (st, .Rval [v'])
  | [.Fun x e] => (st, .Rval [.Closure env x e])
  | [.App o_ es'] =>
    match _hfc : fix_clock st (evaluate st env es'.reverse) with
    | (st', .Rval vs) =>
      match getOpClass o_ with
      | .FunApp =>
        match do_opapp vs.reverse with
        | some (env', e) =>
          if _hc : st'.clock == 0 then (st', .Rerr (.Rabort .Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', .Rerr (.Rabort .Rtype_error))
      | .Force =>
        match dest_thunk vs.reverse st'.refs with
        | .BadRef => (st', .Rerr (.Rabort .Rtype_error))
        | .NotThunk => (st', .Rerr (.Rabort .Rtype_error))
        | .IsThunk .Evaluated val_ => (st', .Rval [val_])
        | .IsThunk .NotEvaluated f =>
          match do_opapp [f, .Conv none []] with
          | some (env', e) =>
            if _hc : st'.clock == 0 then (st', .Rerr (.Rabort .Rtimeout_error))
            else
              match evaluate (dec_clock st') env' [e] with
              | (st2, .Rval vs2) =>
                match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, .Rerr (.Rabort .Rtype_error))
                | some refs => ({ st2 with refs := refs }, .Rval vs2)
              | (st2, .Rerr e) => (st2, .Rerr e)
          | none => (st', .Rerr (.Rabort .Rtype_error))
      | .EvalOp =>
        match _hfc1 : fix_clock st' (do_eval_res vs.reverse st') with
        | (st1, .Rval (env1, decs)) =>
          if _hc : st1.clock == 0 then (st1, .Rerr (.Rabort .Rtimeout_error))
          else
            match fix_clock (dec_clock st1)
                    (evaluate_decs (dec_clock st1) env1 decs) with
            | (st2, .Rval env2) =>
              match declare_env st2.eval_state_field (extend_dec_env env2 env1) with
              | some (x, es2) =>
                ({ st2 with eval_state_field :=
                    reset_env_generation st'.eval_state_field es2 }, .Rval [x])
              | none => (st2, .Rerr (.Rabort .Rtype_error))
            | (st2, .Rerr (.Rabort a)) => (st2, .Rerr (.Rabort a))
            | (st2, .Rerr e) =>
              ({ st2 with eval_state_field :=
                  reset_env_generation st'.eval_state_field st2.eval_state_field },
               .Rerr e)
        | (st1, .Rerr e) => (st1, .Rerr e)
      | .Simple =>
        match do_app (st'.refs, st'.ffi) o_ vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi_), r) =>
          ({ st' with refs := refs, ffi := ffi_ }, list_result r)
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Log l e1 e2] =>
    match _hfc : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match _hlog : do_log l v1.head! e2 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some (.Exp e) => evaluate st' env [e]
      | some (.Val v') => (st', .Rval [v'])
    | (st', .Rerr e) => (st', .Rerr e)
  | [.If e1 e2 e3] =>
    match _hfc : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v') =>
      match _hif : do_if v'.head! e2 e3 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some e => evaluate st' env [e]
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Mat e pes] =>
    match _hfc : fix_clock st (evaluate st env [e]) with
    | (st', .Rval v') =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v'.head! then
        evaluate_match st' env v'.head! pes bind_exn_v
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Let xo e1 e2] =>
    match _hfc : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v') =>
      evaluate st' (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Letrec funs e] =>
    if ALL_DISTINCT (funs.map fun (x, _, _) => x) then
      evaluate st (.mk (build_rec_env funs env env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Tannot e _] => evaluate st env [e]
  | [.Lannot e _] => evaluate st env [e]
  | e1 :: e2 :: es' =>
    match _hfc : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match evaluate st' env (e2 :: es') with
      | (st'', .Rval vs) => (st'', .Rval (v1.head! :: vs))
      | (st'', .Rerr e) => (st'', .Rerr e)
    | (st', .Rerr e) => (st', .Rerr e)
  termination_by (st.clock, sizeOf es)
  decreasing_by
    all_goals first
      | (apply lex_le_lt (Nat.le_refl _); (try simp only [list_sizeOf_reverse]); simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := pat_sizeOf_pos ‹_›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List exp›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List dec›; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); simp <;> omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; have := fix_clock_clock_le _hfc1;
         simp [dec_clock] at *; omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; simp [dec_clock] at *; omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); rw [do_log_exp _hlog]; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc)
         rcases do_if_exp _hif with h | h <;> rw [h] <;> simp <;> omega)

def evaluate_match {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (val_ : v) (pes : List (pat × exp)) (err_v : v) :
    cml_state ffi × result (List v) v :=
  match pes with
  | [] => (st, .Rerr (.Rraise err_v))
  | (p, e) :: pes' =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p val_ [] with
      | .No_match => evaluate_match st env val_ pes' err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  termination_by (st.clock, sizeOf pes)
  decreasing_by
    all_goals first
      | (apply lex_le_lt (Nat.le_refl _); (try simp only [list_sizeOf_reverse]); simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := pat_sizeOf_pos ‹_›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List exp›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List dec›; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); simp <;> omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; have := fix_clock_clock_le _hfc1;
         simp [dec_clock] at *; omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; simp [dec_clock] at *; omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); rw [do_log_exp _hlog]; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc)
         rcases do_if_exp _hif with h | h <;> rw [h] <;> simp <;> omega)

def evaluate_decs {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (ds : List dec) : cml_state ffi × result sem_env v :=
  match ds with
  | [] => (st, .Rval (.mk nsEmpty nsEmpty))
  | [.Dlet _ p e] =>
    if ALL_DISTINCT (pat_bindings p []) && every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', .Rval v') =>
        (st', match pmatch env.c st'.refs p v'.head! [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval (.mk (alist_to_ns new_vals) nsEmpty))
      | (st', .Rerr err) => (st', .Rerr err)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dletrec _ funs] =>
    (st,
     if ALL_DISTINCT (funs.map fun (x, _, _) => x) &&
        funs.all fun (_, _, e) => every_exp (one_con_check env.c) e then
       .Rval (.mk (build_rec_env funs env nsEmpty) nsEmpty)
     else .Rerr (.Rabort .Rtype_error))
  | [.Dtype _ tds] =>
    if tds.all check_dup_ctors then
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
       .Rval (.mk nsEmpty (build_tdefs st.next_type_stamp tds)))
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dtabbrev _ _ _ _] =>
    (st, .Rval (.mk nsEmpty nsEmpty))
  | [.Denv n] =>
    match declare_env st.eval_state_field env with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some (x, es') =>
      ({ st with eval_state_field := es' }, .Rval (.mk (nsSing n x) nsEmpty))
  | [.Dexn _ cn ts] =>
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
     .Rval (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp))))
  | [.Dmod mn ds'] =>
    match evaluate_decs st env ds' with
    | (st', r) =>
      (st', match r with
        | .Rval env' => .Rval (.mk (nsLift mn env'.v_) (nsLift mn env'.c))
        | .Rerr err => .Rerr err)
  | [.Dlocal lds ds'] =>
    match _hfc : fix_clock st (evaluate_decs st env lds) with
    | (st1, .Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds'
    | (st1, .Rerr e) => (st1, .Rerr e)
  | d1 :: d2 :: ds' =>
    match _hfc : fix_clock st (evaluate_decs st env [d1]) with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e)
  termination_by (st.clock, sizeOf ds)
  decreasing_by
    all_goals first
      | (apply lex_le_lt (Nat.le_refl _); (try simp only [list_sizeOf_reverse]); simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := pat_sizeOf_pos ‹_›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List exp›; simp <;> omega)
      | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List dec›; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); simp <;> omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; have := fix_clock_clock_le _hfc1;
         simp [dec_clock] at *; omega)
      | (apply lex_lt; have := fix_clock_clock_le _hfc; simp [dec_clock] at *; omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc); rw [do_log_exp _hlog]; simp <;> omega)
      | (apply lex_le_lt (fix_clock_clock_le _hfc)
         rcases do_if_exp _hif with h | h <;> rw [h] <;> simp <;> omega)
end

theorem dec_clock_clock {ffi : Type} (s : cml_state ffi) : (dec_clock s).clock = s.clock - 1 := rfl

open Lean Elab Tactic Meta in
/-- Internal proof automation used for the evaluator lemmas. -/
elab "fc_facts" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOf ``fix_clock then
      let stx ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| have := fix_clock_clock_le $stx))

macro "clean_step" : tactic => `(tactic| (
  (try simp [List.attach_map_val] at *) <;>
  split_ands_hyps <;> subst_vars <;> eq_merge))

set_option maxHeartbeats 2000000 in
theorem evaluate_clock_aux {ffi : Type} :
    (∀ (s1 : cml_state ffi) (env : sem_env) (e : List exp) (s2 : cml_state ffi)
      (r : result (List v) v),
      evaluate s1 env e = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : cml_state ffi) (env : sem_env) (ds : List dec) (s2 : cml_state ffi)
      (r : result sem_env v),
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : cml_state ffi) (env : sem_env) (val_ : v) (p : List (pat × exp)) (v' : v)
      (s2 : cml_state ffi) (r : result (List v) v),
      evaluate_match s1 env val_ p v' = (s2, r) → s2.clock ≤ s1.clock) := by
  apply evaluate.mutual_induct
  all_goals intros
  all_goals rename_i s2 r h
  all_goals first | rw [evaluate.eq_def] at h | rw [evaluate_decs.eq_def] at h | rw [evaluate_match.eq_def] at h
  all_goals dsimp only at h
  all_goals (repeat' split at h)
  all_goals clean_step
  all_goals clean_step
  all_goals clean_step
  all_goals clean_step
  all_goals try contradiction
  all_goals fc_facts
  all_goals ih_facts
  all_goals (try simp only [dec_clock_clock] at *)
  all_goals try omega
  all_goals try contradiction
  all_goals simp_all
  all_goals omega

theorem fix_clock_of_le {ffi α : Type} (s : cml_state ffi) (p : cml_state ffi × α)
    (h : p.1.clock ≤ s.clock) : fix_clock s p = p := by
  obtain ⟨a, b⟩ := p
  simp only at h
  simp [fix_clock, h]

-- Theorem stubs

/- HOL4:
Theorem evaluate_clock:
  (∀(s1:'ffi state) env e r s2. evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env v p v' r s2. evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env ds r s2. evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock)
-/
theorem evaluate_clock {ffi : Type} :
    (∀ (s1 : cml_state ffi) (env : sem_env) (e : List exp) (s2 : cml_state ffi)
      (r : result (List v) v),
      evaluate s1 env e = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : cml_state ffi) (env : sem_env) (val_ : v) (p : List (pat × exp)) (v' : v)
      (s2 : cml_state ffi) (r : result (List v) v),
      evaluate_match s1 env val_ p v' = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : cml_state ffi) (env : sem_env) (ds : List dec) (s2 : cml_state ffi)
      (r : result sem_env v),
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) :=
  ⟨evaluate_clock_aux.1, evaluate_clock_aux.2.2, evaluate_clock_aux.2.1⟩
/- HOL4:
Theorem fix_clock_evaluate:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds
-/
theorem fix_clock_evaluate {ffi : Type}
    (s1 : cml_state ffi) (env : sem_env) (e : List exp) (ds : List dec) :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds :=
  ⟨fix_clock_of_le _ _ (evaluate_clock_aux.1 _ _ _ _ _ rfl),
   fix_clock_of_le _ _ (evaluate_clock_aux.2.1 _ _ _ _ _ rfl)⟩
/- HOL4:
Theorem fix_clock_do_eval_res:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s
-/
theorem fix_clock_do_eval_res {ffi : Type}
    (s : cml_state ffi) (vs : List v) :
    fix_clock s (do_eval_res vs s) = do_eval_res vs s := by
  apply fix_clock_of_le
  unfold do_eval_res
  split <;> simp
