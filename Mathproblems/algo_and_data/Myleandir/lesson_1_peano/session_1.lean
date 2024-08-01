

-- We want real numbers and their basic properties
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Choose.Basic
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw[mul_comm a b]
  rw[mul_assoc b a c]

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw[h]


-- 定义后继函数 succ
--注意succ空格，不管有没有空格.在后面的所有引用初都要加空格
def succ(n : ℕ) : ℕ := n + 1

-- example of a theroem
theorem one_eq_one : 1=1 := by
  rfl
-- 定义定理：1 = succ(0)
theorem one_eq_succ_zero  : 1=succ (0) := by
  rfl
-- 定义定理：2 = succ(1)
theorem two_eq_succ_one : 2 = succ (1) := by
  rfl
theorem three_eq_succ_two  : 3=succ (2) := by
  rfl
-- 定义定理：2 = succ(1)
theorem four_eq_succ_three : 4 = succ (3) := by
  rfl
example : 2 = succ (succ 0) := by
  rw[← one_eq_succ_zero]
  rw[← two_eq_succ_one]


-- add_zero is defined in
-- package Mathlib.Data.Nat.Cast.Basic



example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [add_zero]

theorem add_succ(a d : ℕ ) :a+ succ (d) = succ (a + d) := by
  rfl

theorem succ_eq_add_one n : succ n = n + 1 := by
  rw[one_eq_succ_zero,add_succ,add_zero]

example : (2 : ℕ) + 2 = 4 := by
  rw[four_eq_succ_three]
  rw[three_eq_succ_two]
  --注意，下面的数字和后面中括号里面的内容之间不要空格
  nth_rewrite 2[two_eq_succ_one]
  rw[add_succ]
  nth_rewrite 1[← succ_eq_add_one]
  rfl

theorem custom_zero_add (n : ℕ) : 0 + n = n := by
  induction n    --直接使用这句话会找不到tactic策略: induction n with d hd
  rfl
  rw[zero_add]

-- theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
--   induction b
--   rw[add_zero]
--   rw[add_zero]
--   nth_rewrite 1[← add_assoc]
--   rw[a✝]
  -- rw[← succ_eq_add_one]
--Idon't know how!
