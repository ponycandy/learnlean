import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield

example (A B : Prop) (hB : B) : A → (A ∧ B) := by
{
  intro h1
  exact And.intro h1 hB
}
example (A B : Prop) (hA : A) (h : A → B) : B := by
{
  revert hA
  assumption
}

example (A B : Prop) (h : A) (hAB : A → B) : B := by
{
  revert h
  assumption
}
-- example (A B C D E F G H I : Prop) (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
-- {

-- }
example (A B : Prop) (h : A ↔ B) : B ↔ A := by
{
  symm at h
  assumption
}
example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
{
  trans h₁ h₃
}

example (A : Prop) : ¬A ∨ A := by
{
  by_cases h :A--就是假设A成立和A不成立下的分别证明
  exact Or.inr  h
  exact Or.inl h

}
-- example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
-- {
--   have lemma not_not (A : Prop) : ¬¬A ↔ A
-- }
