import Lean
open Lean Elab Tactic

/-
  Phase 2: Tactics as syntactic wrappers.
  We define tactics that simply run other tactics. You'll see:
  - `elab "name" : tactic => do ...`  (register a tactic that runs when the user writes "name")
  - `evalTactic (← `(tactic| ...))`   (build a tactic from quoted syntax and run it)
  - `first | t1 | t2`                 (try t1; if it fails, try t2)
-/

-- -----------------------------------------------------------------------
-- Minimal wrapper: run a single built-in tactic
-- -----------------------------------------------------------------------

elab "my_trivial" : tactic => do
  evalTactic (← `(tactic| trivial))

example : True := by my_trivial

-- Same pattern, different tactic
elab "my_rfl" : tactic => do
  evalTactic (← `(tactic| rfl))

syntax "my_rfl2" : tactic

elab_rules : tactic
  | `(tactic| my_rfl2) => do
      evalTactic (← `(tactic| rfl))

example (n : Nat) : n = n := by my_rfl

-- The quotation `(tactic| ...) parses the ... as tactic syntax; ← runs it and gives you
-- a value (a tactic) that you pass to evalTactic to run in the current goal.

-- -----------------------------------------------------------------------
-- Wrapper that runs a sequence of tactics
-- -----------------------------------------------------------------------

elab "my_conj_triv" : tactic => do
  evalTactic (← `(tactic| constructor; all_goals trivial))

example : True ∧ True := by my_conj_triv

-- -----------------------------------------------------------------------
-- Wrapper that tries alternatives (first | t1 | t2)
-- -----------------------------------------------------------------------

elab "my_assumption" : tactic => do
  evalTactic (← `(tactic| first | assumption | exact ‹_›))

example (P : Prop) (h : P) : P := by my_assumption

-- -----------------------------------------------------------------------
-- Wrapper with a fixed sequence (intro then close)
-- -----------------------------------------------------------------------

elab "my_intro_assump" : tactic => do
  evalTactic (← `(tactic| intro h; exact h))

example (P : Prop) : P → P := by my_intro_assump

-- -----------------------------------------------------------------------
-- Exercises
-- -----------------------------------------------------------------------
/- Define the following tactics (uncomment the examples and fix the tactic so the proof works).
   Hint: use the same pattern: elab "name" : tactic => do evalTactic (← `(tactic| ...)).
-/

-- 1. A tactic that runs `rfl` (you can rename to avoid clashing with my_rfl above, e.g. "ex_rfl")
-- example (a : Nat) : a = a := by sorry

-- 2. A tactic that runs `constructor` then `all_goals trivial` (for True ∧ True style goals)
-- example : True ∧ True := by sorry

-- 3. A tactic that tries `trivial`, and if that fails, runs `rfl`
-- example : True := by sorry
-- example (n : Nat) : n = n := by sorry

-- 4. A tactic that runs `intro` then `assumption` (for goals of the form P → P with P in context)
-- example (Q : Prop) (hQ : Q) : Q → Q := by sorry

-- 5. Combine two tactics: define "trivial_or_rfl" that tries my_trivial, and if it fails runs my_rfl.
--    (Use first | my_trivial | my_rfl so both of the above wrappers are used in one tactic.)
-- example : True := by trivial_or_rfl
-- example (n : Nat) : n = n := by trivial_or_rfl

-- 6. Define a tactic that runs constructor then all_goals rfl (for goals that are a conjunction of definitional equalities).
-- example (a b : Nat) : a = a ∧ b = b := by sorry

-- 7. Define a tactic that does intro twice then assumption (for goals P → Q → R when R is in context).
-- example (P Q R : Prop) (hR : R) : P → Q → R := by sorry

-- 8. Define a tactic that tries assumption; if that fails, runs constructor then all_goals assumption.
--    So it closes either a single goal from the context or a conjunction of goals from the context.
-- example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by sorry
