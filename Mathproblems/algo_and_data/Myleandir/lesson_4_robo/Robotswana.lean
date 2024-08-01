import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators


open Nat Matrix BigOperators--相当于省一个命名空间的作用
--但是节约不了类型转化
-- def Matrix.E {n : ℕ} (i j : Fin n) : Matrix ℕ  ℕ  ℝ :=
--   stdBasisMatrix i j (1 : ℝ)
--上面这个就是我们在没有任何参考情况下琢磨出来的函数用法
def Matrix.E {n : ℕ} (i j : Fin n) : Matrix (Fin n)  (Fin n)  ℝ:=
  stdBasisMatrix i j (1 : ℝ)
--这个是我们参考了已有的使用案例下的用法
--所以，我认为不存在着不适用参考就能够学会lean咋用的方法，我们的
--大战略方向就是找更多的习题和证明
theorem smul_ebasis {n : ℕ} (A : Matrix (Fin n)  (Fin n)  ℝ  ) (i j :Fin n) :
A i j • E i j = stdBasisMatrix i j (A i j) := by
{
  unfold E
  simp
}
example {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
{
  unfold E
  simp [h]
}
example {n : ℕ} (i j k : Fin n) : E i j * E j k = E i k  := by
{
  unfold E
  simp
}
example {n : ℕ} (A : Matrix (Fin n)  (Fin n)  ℝ ) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
{
  unfold E
  simp
  simp_rw [smul_ebasis]
}

def iden (n : Nat) : Matrix ℕ  ℕ   ℝ  :=
λ i j => if i = j then 1.0 else 0.0
--第一个Matrix ℕ  ℕ   ℝ  说的是矩阵的类型
--:=后面是矩阵的具体定义，要限制矩阵的大小可以在这里约束
#check (iden 3) 1 1
#eval ((iden 3) 1 1)
