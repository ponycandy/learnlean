import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Order.Floor

#check ℕ+
#check (0:ℕ )
#check (0:ℕ+)
#check (1:ℕ+)
#check (1:ℕ )
#check (1:pos_num)
#check  (1:ℕ).toPNat
#check (0:ℕ).toPNat
#check (1:ℝ)

variable(tempfloorring :FloorRing ℝ)
#check tempfloorring.floor 3.2
#check (tempfloorring.floor 3.2).toNat

#check ((tempfloorring.floor 3.2).toNat).toPNat

#check (1:ℕ).toPNat
#check Nat.toPNat 1
--a function with hypothesis as input
--hypothesis is by decide...
variable (midnum:ℕ := (tempfloorring.floor 3.2).toNat)

--how to prove that a type can be conversion?
example : midnum>0 := by
{
  have h1: tempfloorring.floor 3.2=3 := by
  {
    simp
    rw[Int.floor_eq_iff]
    constructor
    ring
    linarith
    ring
    linarith
  }
  have h2 : tempfloorring.floor 3.2 >0 := by
  {
    rw[h1]
    tauto
  }
  have h3: midnum= tempfloorring.floor 3.2 := by
  {
    --do not deem cast type as cast type
    --instead ,deem it as a proof
    unfold optParam
  }
}

#check Nat.toPNat (1:ℕ)
-- def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
--   ⟨n, h⟩
variable (h:0<1)
#check Nat.toPNat (1:ℕ) (h)--this is how this function work!
#check 1:(Nat.toPNat (1:ℕ) (h)) --return ⟨ n,h⟩ as ℕ+
#check (Nat.toPNat (1:ℕ) (h)).1
#check (Nat.toPNat (1:ℕ) (h)).2

-- 到这里我们终于要思考类型论的一个底层问题了，那就是类型的校验
-- 之前我们的模型里面这一部分是用f()来表示0和1的
-- 实际的类型中是如何校验一个对象是否可以匹配类型的
--try original form of pNat:
#check ( 1: {n| n>0})
#check (1:Nat)
#check (1:ℕ+)
--why can I do .1 on 1:ℕ+ but not on 1:Nat?

#check {n // n>0}
--// means what? satisfied?
#check (1:{n // n>0})
#check {n | n>0}
#check 1:Pos
#check (1:ℕ ).toPNat'
--can I use Type conversion like set theory?
--no, but there is a way to do
--type conversion or what we called Coercions
--https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html

instance : Coe Int Nat where
  coe x := x.toNat
-- instance : Coe Nat :=
-- { addsup := Nat.add }
#check Nat.toPNat (1) (h: 1>0)
--this is the real input of Nat.toPNat
