import Lean
open Lean Elab Tactic

/-
  tactics that inspect the proof goal a little.
-/

elab "prove_true" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
  else
    throwError "goal is not True"
