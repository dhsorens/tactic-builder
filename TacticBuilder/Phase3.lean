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
