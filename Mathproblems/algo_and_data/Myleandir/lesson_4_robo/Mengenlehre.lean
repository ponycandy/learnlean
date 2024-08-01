
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Cast.NeZero

example (X Y : Set ℕ): 𝒫 X ∪ 𝒫 Y ⊆ 𝒫 (X ∪ Y) := by
{
  intro A
  intro hA
  rw [Set.mem_union] at hA
  simp_rw [Set.mem_powerset_iff] at *
  cases' hA with Ha1 Ha2
  apply Set.subset_union_of_subset_left
  assumption
  apply Set.subset_union_of_subset_right
}
example : ¬Disjoint ({n : ℤ | ∃ k, n = 2 * k} : Set ℤ) ({3, 5, 6, 9, 11} : Set ℤ) := by
{
  -- unfold Disjoint
  -- push_neg--此处的符号≤应当实例化为⊆
  rw [Disjoint]
  rw [not_forall]
  use {6}
  simp
  use 3
  simp
}
example : {2, 7} ⊆ {n : ℕ | n = 2 ∨ (n ≤ 10 ∧ Odd n)} := by
{
  rw [Set.setOf_or, Set.setOf_and]
  intro x
  intro hx
  rcases hx with hx | hx
  left
  trivial
  right
  constructor
  rw[hx]
  trivial
  rw[hx]
  trivial
}

example (S : Set ℤ) : { x ∈ (S : Set ℤ) | 0 ≤ x} ⊆ S := by
{
  simp
}

example : 3 ∈ {n : ℕ | Odd n} := by
{
  simp
  trivial
}
