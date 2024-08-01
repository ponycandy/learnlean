import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield

example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  have h4 : x ∈ B := h1 h3
  have h5 : x ∈ C := h2 h4
  exact h5

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4

theorem Subset_refl (A : Set U) : A ⊆ A := by
  intro x
  intro h
  exact h

theorem Subset_trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x
  intro h3
  have h4: x ∈ B := h1 h3
  have h5: x ∈ C := h2 h4
  exact h5
