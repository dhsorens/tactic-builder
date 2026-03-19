/-
  Phase 1: Proofs and proof terms.
  Each block shows the same theorem proved with tactics (`by ...`) and as a direct proof term.
  Understanding this correspondence is the basis for building tactics that construct proof terms.
-/

-- Implication: applying a hypothesis
example (P Q : Prop) (h₁ : P) (h₂ : P → Q) : Q := by
  exact h₂ h₁

example (P Q : Prop) (h₁ : P) (h₂ : P → Q) : Q :=
  h₂ h₁

-- Conjunction: destruct with rcases, build with constructor
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => match h with | ⟨hP, hQ⟩ => ⟨hQ, hP⟩

-- Disjunction: intro left/right, eliminate with rcases
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hP | hQ
  · right; exact hP
  · left; exact hQ

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl hP => Or.inr hP
  | Or.inr hQ => Or.inl hQ

-- Negation: intro gives a function, using ¬P is applying it
example (P : Prop) (h : P → False) : ¬P := by
  intro p
  exact h p

example (P : Prop) (h : P → False) : ¬P :=
  h

-- Iff: two implications
example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  rcases h with ⟨pq, qp⟩
  constructor
  · exact qp
  · exact pq

example (P Q : Prop) (h : P ↔ Q) : Q ↔ P :=
  match h with
  | ⟨pq, qp⟩ => ⟨qp, pq⟩

-- True and False
example : True := by exact trivial
example : True := trivial

example (P : Prop) (h : False) : P := by exact False.elim h
example (P : Prop) (h : False) : P := False.elim h

-- Universal quantification: intro/apply
example (α : Type) (P : α → Prop) (x : α) (h : ∀ z, P z) : P x := by
  exact h x

example (α : Type) (P : α → Prop) (x : α) (h : ∀ z, P z) : P x :=
  h x

-- Existential: use gives a witness, obtain/rcases eliminates
example (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x := by
  exact ⟨a, ha⟩

example (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x :=
  ⟨a, ha⟩

-- Eliminate ∃: get witness and proof; use the proof (hn : n = 0) to build a goal in Prop.
-- (Lean only lets us eliminate ∃ into Prop, not into Type like Nat.)
example (h : ∃ x : Nat, x = 0) : 0 = 0 := by
  rcases h with ⟨n, hn⟩
  exact Eq.trans (Eq.symm hn) hn

example (h : ∃ x : Nat, x = 0) : 0 = 0 :=
  match h with | ⟨_, hn⟩ => Eq.trans (Eq.symm hn) hn

-- Definitional equality: both sides are the same once reduced
example (n : Nat) : n = n := by rfl
example (n : Nat) : n = n := rfl

-- Using an equality to substitute (transport): prove p b from h : a = b and hp : p a.
-- Tactic mode ("by ..."): rw [← h] rewrites the goal to p a, then exact hp.
-- Term mode: h ▸ hp is the transport operator (Eq.subst)—the proof-term analogue of "rewrite with h".
example {T} (a b : T) (p : T → Prop) (h : a = b) (hp : p a) : p b := by
  rw [← h]
  exact hp

example {T} (a b : T) (p : T → Prop) (h : a = b) (hp : p a) : p b :=
  h ▸ hp

/- -----------------------------------------------------------------------
   Exercises
   - -----------------------------------------------------------------------
   Below are tactic proofs. Convert each to a direct proof term (no `by`).
   Uncomment and fill in the `sorry` or replace the placeholder.
-/

-- 1. Implication: prove Q from P and P → Q → R and Q → R (or similar chain).
example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact hQR (hPQ hP)
-- Now as a proof term:
-- example (P Q R : Prop) (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=

-- 2. Conjunction: prove P ∧ Q from (P ∧ Q) ∧ R.
example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : P ∧ Q := by
  exact h.1
-- example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : P ∧ Q :=

-- 3. Disjunction: prove P ∨ Q → Q ∨ P (symmetry of ∨).
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · exact Or.inr hP
  · exact Or.inl hQ
-- example (P Q : Prop) : P ∨ Q → Q ∨ P :=

-- 4. Combine: from ∃ x, P x and (∀ y, P y → Q) prove Q.
example (α : Type) (P : α → Prop) (Q : Prop) (hex : ∃ x, P x) (h : ∀ y, P y → Q) : Q := by
  rcases hex with ⟨x, hPx⟩
  exact h x hPx
-- example (α : Type) (P : α → Prop) (Q : Prop) (hex : ∃ x, P x) (h : ∀ y, P y → Q) : Q :=
