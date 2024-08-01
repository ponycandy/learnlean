import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield

theorem Subset_refl (A : Set U) : A ⊆ A := by
  intro x
  intro h
  exact h

theorem Subset_trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x
  intro h3
  have h4: x ∈ B := h1 h3
  have h5: x ∈ C := h2 h4
  exact h5

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h3
  have h4 : x ∈ B := h3 h1
  exact h2 h4

theorem mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rw[mem_compl_iff A x] --如果assumption在推理符号左侧，则施加rw会将它变成theroem的右侧
  rw [mem_compl_iff] at h2 --如果theroem中不包含推理符号（\imp）则不能够使用rw策略
  by_contra h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4


example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left  --可以直接生成一半假设

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  rw[Set.mem_inter_iff] at h
  exact h.right

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x
  intro h
  rw[Set.mem_inter_iff] at h
  exact h.left

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  have h3: x∈ A∩B := And.intro h1 h2
  exact h3

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x
  intro h3
  have h4: x∈ B := h1 h3
  have h5: x∈ C := h2 h3
  exact And.intro h4 h5

theorem inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x
  intro h1
  rw[  Set.mem_inter_iff] at h1
  have h2 : x ∈ A := h1.left
  have h3 : x ∈ B := h1.right
  exact And.intro h3 h2

theorem inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  have h1: A ∩ B ⊆ B ∩ A :=inter_subset_swap A B
  have h2: B ∩ A ⊆ A ∩ B :=inter_subset_swap B A
  rw[antisymm h1 h2]
--注意定理是可以选择hyposess为输入的！下面是第二种输入方法
  -- apply Subset.antisymm
  -- have h1: A ∩ B ⊆ B ∩ A :=inter_subset_swap A B
  -- exact h1
  -- have h2: B ∩ A ⊆ A ∩ B :=inter_subset_swap B A
  -- exact h2
theorem inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply Set.Subset.antisymm -- ((A ∩ B) ∩ C) (A ∩ (B ∩ C))
  intro x
  intro h1
  rw[Set.mem_inter_iff]
  rw[Set.mem_inter_iff] at h1
  have h2 :x ∈ C := h1.right
  have h3 :x ∈ A ∩ B := h1.left
  rw[Set.mem_inter_iff] at h3
  have h4 :x ∈ A := h3.left
  have h5 :x ∈ B := h3.right
  rw[Set.mem_inter_iff]
  have h6: x ∈ A ∧ x ∈ B := And.intro h4 h5
  apply And.intro
  exact h4
  apply And.intro
  exact h5
  exact h2
  intro x
  intro h
  rw[Set.mem_inter_iff]
  rw[Set.mem_inter_iff]
  rw[Set.mem_inter_iff] at h
  rw[Set.mem_inter_iff] at h
  apply And.intro
  apply And.intro
  exact h.left
  exact (h.right).left
  exact (h.right).right
