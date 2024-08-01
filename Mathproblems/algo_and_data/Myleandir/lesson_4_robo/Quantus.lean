import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Cast.NeZero

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
{
  ring
}
example (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
{
  rw [← h₁] at h₃
  rw [h₃] at h₂
  symm at h₂
  assumption
}
example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
{
  rw[h] at g
  exact g
}
example (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
{
  rw[h]
  rw[g]
  ring
}
example : 1 + 1 = 2 := by
{
  rfl
}
theorem even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
{
  unfold Even at *
--   简单来说就是定义展开，之前一直用的是theroem来代替定义
-- 现在可以用unfold来查看定义了
  obtain ⟨r, hr⟩ := h
  use 2*r^2
  rw [hr]
  ring
}
example (a b: ℝ ) (h: a>b):a   >   b :=by
{
  --查看>的定义
  -- unfold > at *
--不行
  -- exact h
  -- simp
  -- rw[symm] at h
}

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
{
  unfold Odd at *
  obtain ⟨s, hs⟩ := h
  use 2*(s+s^2)
  rw[hs]
  ring
}


example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
{
  unfold Odd at *
  unfold Even at *
  intro r h1
  obtain ⟨s, hs⟩ := h1
  use s
  rw[hs]
  ring
}
example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
{
  apply Iff.intro
  intro h1
  push_neg at h1
  exact h1
  intro h1
  push_neg
  exact h1

}
example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
{
  push_neg
  intro n --消除\any符号的方法
  use n
  rw[← Nat.even_iff_not_odd]
  unfold Even
  use n
}
example {People : Type} (h_nonempty : Nonempty People) (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
{
  --不能一上来就intro，所以intro ->符号的规则是，不能拿存在量词符号？
  #check ∃ x, isDrinking x
  by_cases h: ∀ y, isDrinking y
  rcases h_nonempty with ⟨d⟩--没看懂这里的模式匹配
  use d
  intro h1
  assumption
  push_neg at h
  rcases h with ⟨ p,hp⟩--还是没看懂这里的模式匹配
  use p
  intro hp1
  contradiction
}
