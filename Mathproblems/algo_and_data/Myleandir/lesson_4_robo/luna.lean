import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.Tactic.Linarith
example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
{
  rfl
  --整数上的不等式就是这么定义的....
--这里并不是要真的证明，而是需要把这个式子当作公理来用.....
}
theorem custom_pos_iff_ne_zero (n : ℕ) : 0 < n ↔ n ≠ 0 := by
{
  rcases n
  simp
  constructor
  intro
  tauto
  intro
  simp
}
-- example (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
-- {
--   by_contra h1
--   rw[h1] at h
-- --需要能够和h发生相互作用的theroem以生成类型false
-- }
example (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
{
  linarith
  --这玩意儿真不知道哪里出来的，虽然
--整数的不等式已经用上面的example定义了。。。
--所以，究竟从哪里寻找Mathlib中的定义啊，肯定不是互联网
--能查出来吗。。。。。。。
}
example :1.1>1 := by
{

}
