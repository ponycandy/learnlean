import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor
-- import Mathlib.Algebra.Ring
--定义指标集的方法(https://leanprover.github.io/logic_and_proof/sets_in_lean.html)

-- #check Int.floor x
-- def floor_to_nat (x : ℝ) : ℕ+ := Int.toNat ⌊x⌋
variable(f: ℝ → ℝ )
def A (n : ℕ): Set ℝ := {x |  f (x) > 1/n}
#check A 1
#check A f
-- 给变量 A 赋值，例如定义 A 为返回自然数平方根集合的函数
--报错failed to synthesize instance OfNat ℝ 0的原因是没有导入下面这个包：
--import Mathlib.Data.Real.Basic
-- def greaterthanset (n : ℕ+) : Set ℝ :=
--   {x : ℝ |  f (x) > 1/n}
def UnionAll (A : ℕ → Set ℝ) : Set ℝ := { x | ∃ i : ℕ, x ∈ A i }
def InterAll (A : ℕ → Set ℝ) : Set ℝ := { x | ∀ i : ℕ, x ∈ A i }
#check UnionAll (A f)
-- #check LinearOrderedRing ℕ
-- #check @Int.floor
-- #check Int.floor (4:ℤ)--α 是隐参数,也就是实际上的输入3
-- --α 是隐参数,也就是实际上的输入3
-- --set_option diagnostics true
-- -- variable(a:ℤ )
-- #synth FloorRing ℝ
-- #check Real.instFloorRing
-- #check OfNat
-- def Z_toPNat(x:ℤ )(h: x>0 := by decide):ℤ → ℕ+:=1
-- --只定义类型转化，不定义转化方式
-- --只定义类型，不定义计算过程
-- --because it is a subtype....
-- --为什么这么短的路径这么复杂？
-- #check (1:ℕ ).toPNat

-- --上面这个表达集族的方式真的时蛋疼......
-- --记住符号→的右结合性，然后每次输入的类型都是第一个→符号的左侧
-- #check Nat.floor 1
-- variable(somevalue: Nat := Nat.floor 1)
--def customFloor(x:ℝ):ℤ  := max {m ∈ ℤ | m ≤ x }
--custom defination of floor is difficult
--def custom_floor (x: ℝ ): ℝ → ℕ+:=--可计算版本的floor
--this is it!:exists_nat_one_div_lt
#check exists_nat_one_div_lt
theorem invgtzero(n:ℕ) : (n:ℝ )⁻¹ ≥ 0 := by
{
  #check inv_pos
  simp--at least we can check it
}
example (h: Aall={x | f (x) > 0} ): UnionAll (A f)=Aall :=by
{
  have h1 : ∀ x,( f (x) > 0 ↔  ∃ n:ℕ, f (x) > 1/n) :=by
  {
    --There should be a theroem that prove this...
    intro x
    apply Iff.intro
    intro h1
    have h2 := exists_nat_one_div_lt h1
    obtain ⟨n, hn ⟩ :=h2
    use n+1
    rw[gt_iff_lt]
    --about type cast : https://proofassistants.stackexchange.com/questions/4113/how-to-perform-type-conversion-coercion-in-lean-4
    norm_cast at hn
    --这里真的只剩最后一步了...
    --教训是尽量用n+1不要用ℕ+
    --or use simp to cancel conversion!
--it is impossible to use floor because it is not computable
--Let's start our definition form limit
    --    use (realring.floor ((1/(f x)+1)))
        --this isn't working,ℤ can't be convert to ℕ+
        --unconditionally
        --there must be a more clever way to do it
    intro h2
    obtain ⟨n, hn ⟩ :=h2
    simp at hn
    have h5 : (n:ℝ )⁻¹ ≥ 0:= by {simp}
    linarith
    --所以怎么解决这种问题，用子命题+simp叠加解决
  }
  unfold UnionAll
  rw[h]
  unfold A
  simp
  apply Set.Subset.antisymm
  intro x0 hx
  simp
  simp at hx
  simp at h1
  rw[←h1] at hx
  exact hx
  intro x0 hx0
  simp
  simp at hx0
  rw [← gt_iff_lt] at hx0
  rw[h1 x0] at hx0
  simp at hx0
  exact hx0
}
--finally!
--总结：1.不要使用N+ type，使用n+1替代
-- 2.关于type conversion的网站已经贴上去了
-- 3.对假设和目标同时使用simp可以将数据类型转化化简到同一种状态
--4. avoid using Type conversion!
