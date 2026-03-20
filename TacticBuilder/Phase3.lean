import Lean
open Lean Elab Tactic Meta

/-
  Phase 3: Tactics that inspect the proof goal.
  We read the current goal (getMainGoal, goal.getType), branch on its shape,
  and run different tactics or throw helpful errors.
-/

-- -----------------------------------------------------------------------
-- Get the goal and its type
-- -----------------------------------------------------------------------
-- getMainGoal gives an MVarId (the metavariable for the goal).
-- goal.getType gives the goal's type as an Expr (what we're trying to prove).
-- We can then inspect that Expr (e.g. isConstOf, isAppOf) and decide what to do.

elab "prove_true" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
  else
    throwError "goal is not True"

example : True := by prove_true

-- -----------------------------------------------------------------------
-- Branch on goal shape: equality
-- -----------------------------------------------------------------------
-- Eq in Lean is applied: Eq α lhs rhs. So we check with isAppOf ``Eq.

elab "prove_eq_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isAppOf ``Eq then
    evalTactic (← `(tactic| rfl))
  else
    throwError "goal is not an equality"

example (n : Nat) : n = n := by prove_eq_rfl

-- -----------------------------------------------------------------------
-- Branch on goal shape: conjunction (And)
-- -----------------------------------------------------------------------
-- And P Q is an application of ``And to two arguments.

elab "split_and" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isAppOf ``And then
    evalTactic (← `(tactic| constructor))
  else
    throwError "goal is not a conjunction"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  split_and
  · assumption
  · assumption

-- -----------------------------------------------------------------------
-- Combine inspection with a fallback
-- -----------------------------------------------------------------------
-- If the goal is True, prove it; otherwise try rfl (for definitional equalities).

elab "prove_true_or_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
  else
    evalTactic (← `(tactic| rfl))

example : True := by prove_true_or_rfl
example (n : Nat) : n = n := by prove_true_or_rfl

-- -----------------------------------------------------------------------
-- Local context: getLCtx, inferType, isExprDefEq
-- -----------------------------------------------------------------------
-- `getLCtx` (MetaM): the hypotheses and let-bindings in scope for the *current*
-- metavariable — use `goal.withContext` or `withMainContext` so it matches the goal.
--
-- `LocalDecl` entries carry `userName`, `fvarId`, `type`, and `toExpr` (the `Expr` for
-- that hypothesis, suitable for `exact` / `assign`).
--
-- `inferType e` (MetaM): compute the type of an arbitrary expression `e` (elaboration
-- / metavariable state aware). Contrast with `localDecl.type`, which is the recorded
-- type of a hypothesis.
--
-- `isExprDefEq t s` (MetaM): true iff `t` and `s` are *definitionally equal* in the
-- current context (can assign metavariables while unifying). Use it to compare a
-- hypothesis type to `mkConst ``False`, etc. (`isDefEq` is the same function.)

#check Lean.LocalDecl
#check Lean.MVarId.withContext
#check getLCtx
#check inferType
#check isExprDefEq

/-- For each visible local declaration, log its user name and type (tracing must be enabled). -/
elab "trace_locals" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        logInfo m!"local {localDecl.userName} : {← ppExpr localDecl.type}"

example (a _b : Nat) (_ha : a = 0) : True := by
  trace_locals  -- shows in "Messages" / info view when this example is elaborated
  trivial

/-- Close the goal if some hypothesis is definitionally `False`. -/
elab "exact_false_hyp" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let falseTy := mkConst ``False
    for localDecl in (← getLCtx) do
      if (← isExprDefEq localDecl.type falseTy) then
        goal.assign localDecl.toExpr
        return
    throwError "no hypothesis of type False"

example (h : False) : False := by exact_false_hyp

/-- Pick the first hypothesis whose type is defeq to `Nat`, and log `inferType` on its `Expr`. -/
elab "trace_first_nat_hyp" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let natTy := mkConst ``Nat
    for localDecl in (← getLCtx) do
      if (← isExprDefEq localDecl.type natTy) then
        let inferred ← inferType localDecl.toExpr
        logInfo m!"found {localDecl.userName}, inferType gives: {← ppExpr inferred}"
        return
    logInfo "no Nat hypothesis"

example (_n : Nat) : True := by
  trace_first_nat_hyp
  trivial

-- -----------------------------------------------------------------------
-- Exercises
-- -----------------------------------------------------------------------
/- Implement the following. Use getMainGoal, goal.getType, and target.isConstOf / target.isAppOf.
   Uncomment the examples and define your tactic so the proof works.
-/

-- 1. A tactic "prove_false" that only runs when the goal is exactly False; then close with a hypothesis of type False.
--    Hint: find a declaration in the local context (getLCtx) whose type is False (use inferType, isExprDefEq), then exact that expression.
-- example (P : Prop) (h : False) : False := by prove_false

-- 2. A tactic "split_iff" that, when the goal is P ↔ Q, runs constructor (giving two subgoals P → Q and Q → P).
-- example (P Q : Prop) (pq : P → Q) (qp : Q → P) : P ↔ Q := by split_iff; exact pq; exact qp

-- 3. A tactic "try_trivial" that if the goal is True runs exact True.intro, else does nothing (no error).
--    So the goal may remain. Hint: use evalTactic for the True case; in the else branch just return ().
-- example : True := by try_trivial

-- 4. A tactic that if the goal is P ∧ Q runs constructor, otherwise throws an error with the goal type in the message.
--    Use m!"goal is not a conjunction: {target}" for a readable error.
