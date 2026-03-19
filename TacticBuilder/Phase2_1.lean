import Lean
open Lean Elab Tactic

/-
  Phase 2.1: Basic tactics as proof-term builders.

  Phase 1 showed the correspondence between tactic proofs and proof terms:
  e.g. `intro h; exact h` proves P → P and the proof term is `fun h => h`.
  Here we reimplement minimal versions of basic tactics (with arguments where
  useful) so you see that each tactic is just a way to produce a specific
  proof term or to split the goal into subgoals that become subterms.

  We use:
  - `syntax "name " ... : tactic`  to declare tactic syntax that takes arguments
  - `macro_rules` when we only need to rewrite to existing tactic syntax
  - `elab_rules : tactic` and `evalTactic (← \`(tactic| ... $e ...))` when we
    need to splice a user-supplied term or ident into the tactic
-/

-- -----------------------------------------------------------------------
-- intro / fun
-- -----------------------------------------------------------------------
-- Phase 1: proving P → Q by `intro h` then a proof of Q corresponds to the
-- proof term `fun h => <proof of Q>`.

-- my_intro takes one argument (the name for the introduced hypothesis).
-- We expand to `intros` (which accepts ident) rather than `intro` (different syntax).
syntax "my_intro " ident : tactic

macro_rules
  | `(tactic| my_intro $name) => `(tactic| intros $name)

example {T} : T → T := by
  my_intro a
  exact a

-- Same theorem as proof term: fun a => a
example {T} : T → T := fun a => a

-- -----------------------------------------------------------------------
-- exact / the proof term itself
-- -----------------------------------------------------------------------
-- Phase 1: `exact h` proves the goal when the goal equals the type of h.
-- The proof term is exactly the expression you give.

syntax "my_exact " term : tactic

elab_rules : tactic
  | `(tactic| my_exact $e) => do
    evalTactic (← `(tactic| exact $e))

example (P : Prop) (h : P) : P := by my_exact h
example (P : Prop) (h : P) : P := h

-- -----------------------------------------------------------------------
-- rfl / definitional equality
-- -----------------------------------------------------------------------
-- Phase 1: `rfl` proves t = t; the proof term is `rfl` (or `Eq.refl _`).

elab "my_rfl" : tactic => do
  evalTactic (← `(tactic| rfl))

example (n : Nat) : n = n := by my_rfl
example (n : Nat) : n = n := rfl

-- -----------------------------------------------------------------------
-- trivial / True.intro
-- -----------------------------------------------------------------------
-- Phase 1: proving True by `exact trivial`; the proof term is `trivial` or `True.intro`.

elab "my_trivial" : tactic => do
  evalTactic (← `(tactic| exact True.intro))

example : True := by my_trivial
example : True := True.intro

-- -----------------------------------------------------------------------
-- constructor / ⟨ ... , ... ⟩
-- -----------------------------------------------------------------------
-- Phase 1: proving P ∧ Q by `constructor` then proving P and Q separately
-- corresponds to the proof term `⟨proof of P, proof of Q⟩`.

elab "my_constructor" : tactic => do
  evalTactic (← `(tactic| constructor))

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  my_constructor
  · my_exact hP
  · my_exact hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

-- -----------------------------------------------------------------------
-- apply / building an application
-- -----------------------------------------------------------------------
-- Phase 1: to prove Q from f : P → Q we use `exact f h` when we have h : P;
-- the proof term is `f h`. The tactic `apply f` when the goal is Q leaves
-- subgoal P: we're building the term `f ?_` and ask Lean to fill `?_`.

syntax "my_apply " term : tactic

elab_rules : tactic
  | `(tactic| my_apply $e) => do
    evalTactic (← `(tactic| apply $e))

example (P Q : Prop) (f : P → Q) (h : P) : Q := by
  my_apply f
  my_exact h

example (P Q : Prop) (f : P → Q) (h : P) : Q := f h

-- -----------------------------------------------------------------------
-- existential introduction / ⟨a, ha⟩
-- -----------------------------------------------------------------------
-- Phase 1: proving ∃ x, P x by `exact ⟨a, ha⟩` when ha : P a.
-- We implement a tactic that takes the witness and the proof and runs exact ⟨e1, e2⟩.

syntax "my_use " term ", " term : tactic

elab_rules : tactic
  | `(tactic| my_use $e1, $e2) => do
    evalTactic (← `(tactic| exact ⟨$e1, $e2⟩))

example (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x := by my_use a, ha
example (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x := ⟨a, ha⟩

-- -----------------------------------------------------------------------
-- Exercises
-- -----------------------------------------------------------------------
/- The exercises below tie directly to the tactic/proof-term correspondence in Phase 1.
   For each, you are given a proof (tactic and/or term). Implement a tactic that
   captures the same pattern. Use `syntax` + `elab_rules` (or `macro_rules`) and
   `evalTactic (← \`(tactic| ...))` with antiquotations `$e` where you need to
   splice in the user's terms or idents.
-/

-- 1. Phase 1: P → P is proved by intro then assumption; proof term fun p => p.
--    Implement "my_intro_exact" that takes one ident and runs intro name; exact name
--    (so it proves P → P when P is in context and names the introduced hypothesis).
syntax "my_intro_exact " ident : tactic

macro_rules
  | `(tactic| my_intro_exact $name) => `(tactic| intros $name; exact $name)

example (P : Prop) : P → P := by my_intro_exact p
example (P : Prop) : P → P := fun p => p

-- 2. Phase 1: Proving P ∧ Q from hP : P and hQ : Q uses constructor then exact on each goal.
--    Implement "my_conj" that takes two terms t1 and t2 and runs constructor;
--    then exact t1 on the first subgoal and exact t2 on the second.
--    So "my_conj hP hQ" should close P ∧ Q when hP : P and hQ : Q.
syntax "my_conj " term ", " term : tactic

elab_rules : tactic
  | `(tactic| my_conj $t1, $t2) => do
    evalTactic (← `(tactic| constructor; exact $t1; exact $t2))

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by my_conj hP, hQ
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

-- 3. Phase 1: Proving False from h : False uses exact h. Implement "my_ex_false" that
--    takes one term and runs exact on it (for closing a goal that is False using
--    a hypothesis of type False).
syntax "my_ex_false " term : tactic

elab_rules : tactic
  | `(tactic| my_ex_false $e) => do
    evalTactic (← `(tactic| exact $e))

example (_ : Prop) (h : False) : False := by my_ex_false h
example (_ : Prop) (h : False) : False := h

-- 4. Phase 1: Proving ∀ x, P x from h : ∀ x, P x uses exact h (or exact h x for P x).
--    Implement "my_exact_at" that takes two terms (e.g. e, a) and runs exact e a.
--    Use comma in the syntax so the parser accepts two terms: my_exact_at h, x.
syntax "my_exact_at " term ", " term : tactic

macro_rules
  | `(tactic| my_exact_at $e, $a) => `(tactic| exact $e $a)

example (α : Type) (P : α → Prop) (x : α) (h : ∀ z, P z) : P x := by my_exact_at h, x
example (α : Type) (P : α → Prop) (x : α) (h : ∀ z, P z) : P x := h x

-- 5. Phase 1: Transport along an equality is h ▸ hp (prove p b from h : a = b, hp : p a).
--    Implement "my_subst" that takes two terms (h, hp) and runs rw [← h]; exact hp.
--    Use comma in the syntax: my_subst h, hp.
syntax "my_subst " term ", " term : tactic

-- Use rw then exact; the ▸ proof-term form is awkward to build in quotations
elab_rules : tactic
  | `(tactic| my_subst $h, $hp) => do
    evalTactic (← `(tactic| rw [← $h]; exact $hp))

example {T : Type} (a b : T) (p : T → Prop) (h : a = b) (hp : p a) : p b := by my_subst h, hp
example {T : Type} (a b : T) (p : T → Prop) (h : a = b) (hp : p a) : p b := h ▸ hp
