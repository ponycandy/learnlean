import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Cast.NeZero

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

example (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
{
  have k1:= k.left
  have k2:= k.right
  have k3:= h k1
  contradiction
}

example (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
{
  -- have k3:= h k₁
  -- contradiction
    -- suffices g : ¬B by {

    -- }--没搞明白怎么弄

}

example (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
{
  by_contra h
  have h1:= g h
  contradiction
}

example (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
{
  constructor
  intro h1
  intro h2
  --怎么把h1变成逆否命题
  by_contra h3
  have h4 :=h1 h3
  contradiction
  intro h1 x
  by_contra h2
  have hx:= h1 h2
  contradiction
}
example (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
{
  revert h
  contrapose--这玩意能够把命题变成逆否命题
  rw [← Nat.even_iff_not_odd]
  rw [← Nat.even_iff_not_odd]
  apply even_square--之前证明过的theroem

}
example (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
{
  -- unfold Odd at *
  -- obtain ⟨s, hs⟩ := h
  --use what?上面这条路径在自然数空间里面是证明不出来的
  by_contra g
  -- rw[ ← Nat.even_iff_not_odd] at g
  --rw[Nat.even_iff_not_odd n^2] at h
  have d: ¬ Odd (n ^ 2) := by
  {
    rw [← Nat.even_iff_not_odd] at *
    apply even_square
    assumption
  }
  contradiction
}
