/-
  examples of proofs and their corresponding proof terms
-/

-- implication
example (P Q : Prop) (h₁ : P) (h₂ : P → Q) : Q := by
  exact h₂ h₁

example (P Q : Prop) (h₁ : P) (h₂ : P → Q) : Q :=
  h₂ h₁

-- commutativity of ∧
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h =>
    match h with
    | ⟨hP, hQ⟩ => ⟨hQ, hP⟩
