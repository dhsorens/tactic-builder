import Lean
open Lean Elab Tactic

/-
  Phase 4: Typed quotations and antiquotations.
  Quotations are typed: `(term| ...) is term syntax, `(tactic| ...) is tactic syntax.
  Antiquotation $e splices the value e (usually Syntax) into the quotation.
  That lets us build tactic or term syntax from pieces (e.g. a user-supplied term).
-/

-- -----------------------------------------------------------------------
-- Quotations by category
-- -----------------------------------------------------------------------
-- `(term| 1 + 1) has type Syntax (it's term syntax). We don't run it here;
-- we're just showing we can build term syntax. In tactics we use `(tactic| ...).

-- -----------------------------------------------------------------------
-- Antiquotation: splice a parsed piece into a quotation
-- -----------------------------------------------------------------------
-- We declare syntax that takes a term: "my_exact " e:term. The elaborator
-- receives e as Syntax. We build the tactic "exact <e>" with `(tactic| exact $e),
-- then run it. So my_exact h runs exact h.

syntax "my_exact " term : tactic

elab_rules : tactic
  | `(tactic| my_exact $e) => do
    evalTactic (← `(tactic| exact $e))

example (P : Prop) (h : P) : P := by my_exact h

-- Same idea: my_apply e runs apply e.
syntax "my_apply " term : tactic

elab_rules : tactic
  | `(tactic| my_apply $e) => do
    evalTactic (← `(tactic| apply $e))

example (P Q : Prop) (f : P → Q) (h : P) : Q := by
  my_apply f
  my_exact h

-- -----------------------------------------------------------------------
-- Building a term and using it in a tactic
-- -----------------------------------------------------------------------
-- We can build term syntax and splice it into a tactic. Here we always
-- prove True by building the term True.intro and running exact.

elab "my_trivial_term" : tactic => do
  let t ← `(term| True.intro)
  evalTactic (← `(tactic| exact $t))

example : True := by my_trivial_term

-- -----------------------------------------------------------------------
-- Taking multiple arguments
-- -----------------------------------------------------------------------
-- You can take several terms and use them in one tactic. Here we take one
-- term (often an application like "f h") and run exact on it.

syntax "my_exact2 " term : tactic

elab_rules : tactic
  | `(tactic| my_exact2 $e) => do
    evalTactic (← `(tactic| exact $e))

-- User supplies the full term (e.g. the application f h)
example (P Q : Prop) (f : P → Q) (h : P) : Q := by my_exact2 (f h)

-- -----------------------------------------------------------------------
-- Exercises
-- -----------------------------------------------------------------------
/- Implement the following. Use syntax "name " term : tactic (and optionally more terms),
   then elab_rules : tactic | `(tactic| name $e ...) => do evalTactic (← `(tactic| ... $e ...)).
   Uncomment the examples and define your tactic so the proof works.
-/

-- 1. A tactic "my_apply_at " e:term " at " h:term that runs "apply e at h" (apply e at a hypothesis).
-- example (P Q : Prop) (f : P → Q) (h : P) : Q := by my_apply_at f at h

-- 2. A tactic "my_constructor" that runs constructor, then on the first subgoal runs exact with a given term.
--    So we need a variant that takes one term and does constructor; exact t on the first goal.
--    Simpler alternative: a tactic "close_with " t:term that runs exact t (same as my_exact; do it as practice).

-- 3. A tactic that takes two terms a and b and runs "exact a" on the current goal (ignoring b), then "exact b" on the next.
--    So it's like "exact a; exact b". Name it e.g. my_exact_exact.
-- example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by constructor; my_exact_exact p q

-- 4. A tactic "my_symm" that runs rfl if the goal is a = a, and otherwise runs Eq.symm (so goal a = b becomes b = a).
--    Hint: use a single term for the equality proof: my_symm runs Eq.symm ?_; the goal should become b = a and the ?_ is a = b. So actually "apply Eq.symm" or "exact Eq.symm h" if we had h. For "goal becomes b = a" we need apply Eq.symm. So just a tactic that runs apply Eq.symm (no argument). That doesn't need antiquotations. So instead: a tactic that takes a term e (an equality proof) and runs exact Eq.symm e.
-- example (a b : Nat) (h : a = b) : b = a := by my_symm h
