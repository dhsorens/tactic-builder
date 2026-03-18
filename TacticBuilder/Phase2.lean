import Lean
open Lean Elab Tactic

/-
  first tactics - just syntactic wrappers
-/

elab "my_assumption" : tactic => do
  evalTactic (← `(tactic| first | assumption | exact ‹_›))

elab "my_trivial" : tactic => do
  evalTactic (← `(tactic| trivial))
