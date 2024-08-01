
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- An $n$-dimensional vector is nothing but a function out of `Fin n`. For instance
-- a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
-- `x i : ℝ`. We can represent such a vector as `![x_1, ..., x_n]`.

-- Under the hood, `![a, b, c]` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.
-- where `Matrix.vecCons : α → (Fin n → α) → Fin (Nat.succ n) → α`

-- Since vectors are functions, we can define their addition and scalar multiplication pointwise.

example : ![(Real.sqrt 3)/2, 1/2] + ![-(Real.sqrt 3)/2, 1/2] = ![0, 1] := by
{
--how is add defined for this Type?
--I'll find out
  simp
  ring_nf
}
theorem  one_empty {α : Type*} [One α] : (1 : Fin 0 → ℝ) = ![] := by
{
--what the hell is this?
  apply Matrix.empty_eq _
}
example {x₀ x₁ : ℝ} (h : ![x₀, x₁] = 0) : ![-x₀, -x₁] = 0 := by
{
  simp [Matrix.neg_cons]
  constructor
  --kan budong1
}
