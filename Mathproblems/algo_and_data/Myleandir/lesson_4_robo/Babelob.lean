import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Defs
-- import Mathlib.Algebra.BigOperators.Group.Finset

-- set_option diagnostics true
--Finset.sum Finset.univ f
example (n : ℕ) : (∑ i : Fin n, (0 + 0)) = 0 := by
{
  #check Fin.mk--确认一下构造函数的类型
 -- #eval (∑ x in ({1,2} : Set ℕ ), (0))
  simp
}
example  (n : ℕ) : (∑ i : Fin n, 2) = 2 * n := by
{
  --为什么不能够写成∑ i ∈  Fin n, 2
  --因为类型上来看，Fin n不是一个Set，而是一个structure
--这是我们做lean4的时候不适应的一个地方，实际的类型和想象的类型不一致
 -- #check Finset.sum Finset.univ n,2=2*n
  simp
  ring
}

example (n : ℕ) : ∑ i : Fin n, ((1+i):Nat) = n + (∑ i : Fin n, i:Nat) := by
{
--在复杂的变量式中思考类型和对象关系太累了.........
--最好只是把他们当成佐证
--作为形式化实际问题时候的辅助
--也就是如果报错了，可以按照类型论去修正
  rw [Finset.sum_add_distrib]
  simp
}
--先跳过了，确实搞不定报错
example  (n : ℕ) :2 * (∑ i : Fin (n + 1), i:Nat) = n * (n + 1) := by
{
--这个还是一样的道理，找不到报错
  induction' n with d hd
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  rw [mul_add]
  rw [hd]
  ring
}
example (n : ℕ) : (∑ i : Fin n, (2 * i + 1):Nat) = n ^ 2 := by
{
  induction' n with d hd
  simp
  rw [Fin.sum_univ_castSucc]
  simp
  rw [hd]
  ring
}
example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, (2 ^ (i:Nat) * (((1:Nat) + j):Nat)) =
∑ j : Fin m, ∑ i : Fin n, (2 ^ (i:Nat) * ((1:Nat) + j)) := by
{
  rw [Finset.sum_comm]
}
example (f : Fin n → ℕ) (h : ∀ k, f k ≠ 0) (hn : n > 0) :
∑ i : Fin n, f i ≠ 0 := by
{
  rw [← Nat.pos_iff_ne_zero]
 -- apply Finset.sum_pos
  --apply Finset.sum_pos (fun k _ ↦ Nat.pos_iff_ne_zero.mpr (h k))
}
example (f : Fin n → ℕ) (h : ∃ k : Fin n, f k ≠ 0) (hn : n > 0) :
    ∑ i : Fin n, f i ≠ 0 := by
{
  rw [← Nat.pos_iff_ne_zero]
}
example (m : ℕ) : (∑ i : Fin (m + 1), (i:Nat) ^ 3) = (∑ i : Fin (m + 1), i:Nat) ^ 2 := by
{
  induction' m with d hd
  simp
  --??
}
