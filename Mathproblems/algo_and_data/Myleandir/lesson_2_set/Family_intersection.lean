import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield




theorem mem_pair (t A B : Set U) : t ∈ ({A, B} : Set (Set U)) → (t=A ∨ t=B) := by
{
--注意这里的写法，两个U类型的对象如何生成一个新类型{A,B}
--在类型生成规则中,(A,B)是笛卡尔积，会生成type X type的类型。
--但是{A,B}却是没有定义的!
--此时，生成新类型只需要在{A,B}后面使用冒号写出类型形式就可以了
  intro h1
  cases' h1 with h1a h1b
  exact Or.inl h1a
  exact Or.inr h1b
}



example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
{
  intro x
  intro h
  rw[Set.mem_sInter] at h
  have hA : A ∈ F → x ∈ A := h A
   --这个定义说明了一个很重要的事情
--那就是assumption是可以当成theroem来用的
--所以同样的指令结构：tactic+theroem+input也是可以采用的
  exact hA h1
}

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
{
  intro x
  intro h2
  rw[Set.mem_sInter] at h2
  rw[Set.mem_sInter]
  intro t
  intro h3
  have h4 : t ∈G := h1 h3
  exact h2 t h4 --把assumption当成theroem来用
}
example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
{
  apply Set.Subset.antisymm
  intro x h
  rw[Set.mem_sInter]
  intro t
  intro h1
  rw[mem_pair t A B] at h1
  cases' h1 with h1a h1b
  rw[h1a]
  rw[mem_inter_iff] at h
  exact h.left
  rw[h1b]
  rw[mem_inter_iff] at h
  exact h.right
  intro x h
  rw[mem_sInter] at h
  have h1 : A∈ {A, B}→ x ∈ A := h A
  have h2 : B∈ {A, B}→ x ∈ B := h B
  have h1x: A ∈ {A, B} := by
    rw[mem_pair]
    have h3: A=A := rfl
    exact Or.inl h3
  have h3: x ∈ A := h1 h1x
  have h2x: B ∈ {A, B} := by
    rw[mem_pair]
    have h4: B = B:=rfl
    exact Or.inr h4
  have h4 :x ∈ B := h2 h2x
  have h5 :  x ∈ A ∧  x ∈ B := And.intro h3 h4
  rw[← mem_inter_iff] at h5
  exact h5
}
-- Intersection of a union of families  4


example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
{
  apply Set.Subset.antisymm
  intro x h
  rw[Set.mem_sInter] at h
  rw[Set.mem_inter_iff]
  apply And.intro
  rw[Set.mem_sInter]
  intro t
  intro h1
  have hFG : t ∈ F ∪ G := by
    rw[Set.mem_union]
    exact Or.inl h1
  exact h t hFG
  rw[Set.mem_sInter]
  intro t h1
  have hFG : t ∈ F ∪ G := by
    rw[Set.mem_union]
    exact Or.inr h1
  exact h t hFG
  intro x h
  rw[Set.mem_sInter]
  rw[Set.mem_inter_iff] at h
  rw[Set.mem_sInter] at h
  rw[Set.mem_sInter] at h
  have h1 : ∀ t ∈ F, x ∈ t := h.left
  have h2 : ∀ t ∈ G, x ∈ t := h.right
  intro t h3
  rw[Set.mem_union] at h3
  cases' h3 with ha hb
  exact h1 t ha
  exact h2 t hb
}
