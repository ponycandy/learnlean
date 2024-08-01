import Mathlib.Analysis.Analytic.Basic
import Mathlib.Init.Logic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
example : ∃ f : ℤ → ℤ, ∀ x, f x < x := by
{
  --这是我的想法：
 -- use fun :  ℤ → ℤ := x-1
 --下面是标准解法
  use (fun x ↦ x - 1)
  intro x
  simp--我只能理解为大于号不是我们关心的部分
}

example (x : ℤ) : let f : ℤ → ℤ := fun x ↦ x + 5
∃(g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
{
--let的用法,用鼠标移动到let上面就行
--主要是用来定义functor
--let在目标中时，需要用换行号
  let temp : ℤ → ℤ  := fun x => x-3;
  use temp
  simp --simp
  ring
}
--how to use ext? here is an example

-- variables (A B : Type)
-- variables (f g : A → B)

-- 假设 f 和 g 在所有输入上产生相同的输出
--在Lean中，"ext"（extensionality）
--用于应用函数的外延性原理。外延性原理指出，如果
--两个函数在所有输入上产生相同的输出，那么这两个函数是相等的。
example (h : ∀ x, f x = g x) : f = g := by
{
  ext x -- 应用外延性原理,
  --可以简单的理解为，有一个定理
  --只要每一个点相等，两个函数就相等，相当于是apply这个定理
  #check h x
  exact h x -- 通过假设得出结论
}
--在上面的示例中，我们假设函数"f"和"g"
--在所有输入上产生相同的输出，
--然后使用"ext"来应用外延性原理，
--最后通过这一假设来证明"f = g"。
example : let f : ℚ → ℚ := fun x ↦ 5 * x;
let g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0;
f ∘ g = g ∘ f := by
{
  ext x
  simp
  by_cases h:0 ≤ x --分类
  rw [if_pos]--这个theroem用来消除形式为if...then...的分支
  rw [if_pos]
  ring
  exact h
  exact h
  rw [if_neg h]
  --这个theroem用来消除形式为if...then...的分支
  --不过条件是反的
  rw [if_neg ]
  exact h
}
-- Introduction
-- "
-- A function `g : B → A` is a right inverse of a function `f : A → B` if for all `b : B`,
-- `f (g b) = b`.

-- In this level, you will prove that if `g` is a right inverse of `f`, then the composition `f ∘ g`
-- equals the identity function on `B`.

-- "
--......https://leanprover.github.io/logic_and_proof/functions_in_lean.html
-- variables(f : A -> B)
-- variables(g : B -> A)
--#check RightInverse f g--right_inverse逆函数没有定义


theorem rightInverse_iff_comp {A B : Type}
 {f : A -> B} {g : B -> A} : Function.RightInverse g f ↔ f ∘ g = id := by
{
  constructor
  unfold Function.RightInverse --shit展开不了？
  --定义只能展开一级，一次展开变成leftinverse，再展开一次
  unfold Function.LeftInverse
  intro h1
  -- #check h1
  ext x
  -- unfold Function.RightInverse at *--
  rw [Function.comp_apply]
  rw [h1 x]
  rw [id_eq]
  intro h1
  apply congr_fun


}
example {A B : Type} {f : A -> B} {g : B -> A} : Function.RightInverse g f ↔ Function.LeftInverse f g := by
{
  apply Iff.intro
  intro h1
  unfold Function.LeftInverse
  unfold Function.RightInverse at h1
  unfold Function.LeftInverse at *
  exact h1
  intro h1
  unfold Function.LeftInverse at *
  unfold Function.RightInverse at *
  unfold Function.LeftInverse at *
  exact h1
}
example :
let f : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (m + n, m + 2 * n);
Function.HasRightInverse f := by
{
  unfold Function.HasRightInverse
  unfold Function.RightInverse at *
  unfold Function.LeftInverse at *
  let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (2 * m - n, n - m)
  use g
  intro ⟨x, y⟩--如何引入一个AXB形式的变量
  simp
  ring
  tauto--模式匹配我们确实不太会用
}
example : let f := fun (n : ℤ) ↦ n + 1;
Function.Surjective f  :=by
{
  unfold Function.Surjective
  intro  h1 b
  use b-1
  simp [h1]
}
open Nat
example {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A} (hs : f ∘ g = succ ∘ f)
: Function.Surjective f := by
{
  unfold Function.Surjective
  intro b
  induction' b with n nd
  exact h
  apply congr_fun at hs
  obtain ⟨a, ha⟩ := nd
  use g a
  simp_rw [Function.comp_apply] at hs
  rw[hs]
  simp
  assumption
}
-- example {f : A → B} : Function.Surjective f ↔ Set.range f = univ := by
-- {
--   unfold Function.Surjective
--   unfold Set.range
--   apply Iff.intro
--   intro h1
-- }
example (nonempty_fibre : ∀ b : B, Set.Nonempty (f ⁻¹' { b })) : Function.HasRightInverse f := by
{
    -- Hint "
    --   Since we know that for each `b : B`, the fiber is nonempty, we can choose some element of that fibre using the axiom of choice.
    --   The tactic `choose g hg using nonempty_fibre` creates a function which chooses an `a : A` and `hg` witnesses that `a` is in the fiber of `b`.
    --   "
  choose g hg using nonempty_fibre
  --choose作为通用策略太过于泛化了
  use g
  assumption
}
example (f : A → B) :
    List.TFAE [Function.Surjective f,
    ∀ b : B, Set.Nonempty (f ⁻¹' { b }),
    Function.HasRightInverse f] := by
{
  tfae_have 1 → 2--这策略看起来咋那么复杂呢.....The Following (propositions) Are Equivalent.
  intro h b
  apply h
  tfae_have 2 → 3
  intro h
  use fun b ↦ (h b).choose--没有理解choose的意思！
  --choose从一个存在表述中提取一个元素，类似于obtain
  --#check (h b).choose
  intro b
  simp
  exact (h b).choose_spec
  choose g hg using h
  use g
  assumption
}
