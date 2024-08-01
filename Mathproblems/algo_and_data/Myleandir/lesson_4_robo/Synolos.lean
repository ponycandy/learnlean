import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield


-- theorem Set.mem_univ {A : Type} (x : A) : x ∈ (univ : Set A) := by
-- {
--  simp
--没有看懂这个集合定理，好奇怪的定义
--我一直以为setA是A上的子集，现在看来是包含元素的类型为A的集合
-- }

-- theorem Set.not_mem_empty {A : Type} (x : A) : x ∉ (∅ : Set A) := by
-- {
--这里有意思的是空集的定义
--simp
-- }
example (A B : Set ℕ) : univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
{
--这里注意符号\在实数域是除法的意思，在集合域自动被定义为从集合A中删去集合B中的元素
  rw[Set.diff_inter]
  rw [Set.union_assoc]
  rw [← Set.union_diff_distrib]
  rw [Set.univ_union]
}

-- 注意，上面几个定理都是作为定义使用的，即定义了集合与空集的概念
-- 完全可以当成是公理
