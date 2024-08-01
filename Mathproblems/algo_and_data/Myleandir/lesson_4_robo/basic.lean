import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel

example : True := by
{
  trivial
}
example (A : Prop) (h : False) : A := by
{
  contradiction
}
example (n : ℕ) (h : n ≠ n) : n = 37 := by
{
  contradiction
}
example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
{
 contradiction
}
example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
{
  constructor
  assumption
  assumption
}
example (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
{
  rcases h with ⟨hA, hB,hC⟩
  assumption
}
example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
{
  left
  assumption
}

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
{
  rcases h with h | h
  cases h
  assumption
  assumption
}
example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
{
  rcases h with h | h
  constructor
  left
  assumption
  left
  assumption
  constructor
  rcases h with ⟨ha,hb⟩
  right
  assumption
  rcases h with ⟨ha,hb⟩
  right
  assumption
}
