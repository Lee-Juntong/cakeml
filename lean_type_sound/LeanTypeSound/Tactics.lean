/-
  Small proof-automation helpers used in the proofs of this development.
-/
import Lean

open Lean Elab Tactic Meta

/-- Split every conjunction hypothesis in the context into its components. -/
elab "split_ands_hyps" : tactic => liftMetaTactic fun g => do return [← g.casesAnd]

/-- For every pair of equations `a = b`, `a = c` with the same (non-variable) left-hand side,
add `b = c` and clear the second equation. -/
elab "eq_merge" : tactic => withMainContext do
  let ds := (← getLCtx).decls.toList.filterMap id |>.filter (fun d => !d.isImplementationDetail)
  let mut done : Array FVarId := #[]
  for d1 in ds do
    if done.contains d1.fvarId then continue
    let t1 ← instantiateMVars d1.type
    let some (_, a1, _) := t1.eq? | continue
    if a1.isFVar then continue
    for d2 in ds do
      if d2.fvarId == d1.fvarId || done.contains d2.fvarId then continue
      let t2 ← instantiateMVars d2.type
      let some (_, a2, _) := t2.eq? | continue
      if ← withReducible (isDefEq a1 a2) then
        done := done.push d2.fvarId
        let s1 ← Term.exprToSyntax d1.toExpr
        let s2 ← Term.exprToSyntax d2.toExpr
        evalTactic (← `(tactic| have := (Eq.symm $s1).trans $s2))
  liftMetaTactic fun g => do return [← g.tryClearMany done]

/-- Instantiate every universally quantified implication hypothesis `∀ xs, P xs → Q xs` whose last
premise is an equation, with every equation hypothesis matching that premise (up to reducible
unfolding), adding the conclusions to the context. -/
elab "ih_facts" : tactic => withMainContext do
  let ds := (← getLCtx).decls.toList.filterMap id |>.filter (fun d => !d.isImplementationDetail)
  for d1 in ds do
    let t1 ← instantiateMVars d1.type
    unless t1.isForall do continue
    for d2 in ds do
      let t2 ← instantiateMVars d2.type
      unless t2.isAppOfArity ``Eq 3 do continue
      let r ← withReducible <| observing? do
        let (xs, _, body) ← forallMetaTelescopeReducing t1
        let some hx := xs.back? | failure
        let ht ← inferType hx
        unless (← isDefEq ht t2) do failure
        hx.mvarId!.assign d2.toExpr
        let pf ← instantiateMVars (mkAppN d1.toExpr xs)
        if pf.hasExprMVar then failure
        return (pf, ← instantiateMVars body)
      if let some (pf, ty) := r then
        liftMetaTactic fun g => do
          let g' ← g.assert `ihf ty pf
          let (_, g'') ← g'.intro1P
          return [g'']

/-- Recursively destruct every conjunction, disjunction and existential hypothesis. -/
def splitHypsPred (d : LocalDecl) : MetaM Bool := do
  let t ← instantiateMVars d.type
  return t.isAppOf ``And || t.isAppOf ``Or || t.isAppOf ``Exists

elab "split_hyps" : tactic => liftMetaTactic fun g => g.casesRec splitHypsPred
