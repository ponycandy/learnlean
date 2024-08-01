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
example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h


example (A B : Set U) : B ⊆ A ∪ B := by
  intro x
  rewrite [Set.mem_union]
  intro h
  exact Or.inr h

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x h3
  rw[Set.mem_union] at h3
  cases' h3 with h3A h3B
  exact h1 h3A
  exact h2 h3B


theorem union_subset_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x
  intro h
  rw[Set.mem_union] at h
  rw[Set.mem_union]
  cases' h with ha hb
  exact Or.inr ha
  exact Or.inl hb

theorem union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply Set.Subset.antisymm
  exact union_subset_swap A B
  exact union_subset_swap B A

theorem union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply Set.Subset.antisymm
  intro x
  intro h
  rw[Set.mem_union] at h
  rw[Set.mem_union] at h
  cases' h with ha hb
  cases' ha with haa hab
  rw[Set.mem_union]
  exact Or.inl haa
  rw[Set.mem_union]
  rw[Set.mem_union]
  have habc :  x ∈ B ∨ x ∈ C := Or.inl hab
  exact Or.inr habc
  rw[Set.mem_union]
  rw[Set.mem_union]
  have habc : x ∈ B ∨ x ∈ C := Or.inr hb
  exact Or.inr habc
  intro x
  intro h
  rw[Set.mem_union]
  rw[Set.mem_union]
  rw[Set.mem_union] at h
  rw[Set.mem_union] at h
  cases' h with ha hb
  have hab :  x ∈ A ∨ x ∈ B := Or.inl ha
  exact Or.inl hab
  cases' hb with hbc hbc
  have hab : x ∈ A ∨ x ∈ B := Or.inr hbc
  exact Or.inl hab
  exact Or.inr hbc


theorem compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Set.Subset.antisymm
  intro x h
  rw[Set.mem_compl_iff] at h
  rw[Set.mem_inter_iff]
  apply And.intro
  rw[Set.mem_union] at h
  push_neg at h
  rw[mem_compl_iff]
  exact h.left
  rw[Set.mem_union] at h
  push_neg at h
  rw[mem_compl_iff]
  exact h.right
  intro x h
  rw[mem_compl_iff]
  rw[Set.mem_union]
  push_neg
  rw[← mem_compl_iff]
  rw[← mem_compl_iff]
  rw[Set.mem_inter_iff x Aᶜ  Bᶜ] at h --指定输入看来是有效的
  exact h

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]
  rw[  compl_union Aᶜ Bᶜ]
  rw[compl_compl A]
  rw[compl_compl B]


theorem inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply Set.Subset.antisymm
  intro x h
  rw[Set.mem_inter_iff] at h
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  rw[Set.mem_inter_iff]
  rw[Set.mem_union] at h
  cases' h with h1 h2
  cases' h2 with h2a h2b
  have h3: x ∈ A ∧ x ∈ B := And.intro h1 h2a
  exact Or.inl h3
  have h3: x ∈ A ∧ x ∈ C := And.intro h1 h2b
  exact Or.inr h3
  intro x h
  rw[Set.mem_inter_iff]
  rw[Set.mem_union]
  rw[Set.mem_union] at h
  rw[Set.mem_inter_iff] at h
  rw[Set.mem_inter_iff] at h
  apply And.intro
  cases' h with h1 h2
  exact h1.left
  exact h2.left
  cases' h with h1 h2
  have h2 : x ∈ B := h1.right
  exact Or.inl h2
  have h2 : x ∈ C := h2.right
  exact Or.inr h2


theorem union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply Set.Subset.antisymm
  intro x h
  rw[Set.mem_inter_iff]
  rw[Set.mem_union]
  rw[Set.mem_union] at h
  rw[Set.mem_inter_iff] at h
  cases' h with h1 h2
  have h2:x ∈ A ∨ x ∈ B := Or.inl  h1
  rw[Set.mem_union]
  have h3:x ∈ A ∨ x ∈ C := Or.inl h1
  exact And.intro h2 h3
  rw[Set.mem_union]
  have h2a: x ∈ B := h2.left
  have h2b: x ∈ C := h2.right
  have h3a:x ∈ A ∨ x ∈ B := Or.inr h2a
  have h3b:x ∈ A ∨ x ∈ C := Or.inr h2b
  exact And.intro h3a h3b
  intro x h
  rw[Set.mem_inter_iff] at h
  rw[Set.mem_union] at h
  rw[Set.mem_union] at h
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  have h1:x ∈ A ∨ x ∈ B := h.left
  have h2:x ∈ A ∨ x ∈ C:= h.right
  cases' h1 with h1a h1b
  cases' h2 with h2a h2b
  exact Or.inl h2a
  exact Or.inl h1a
  cases' h2 with h2a h2b
  exact Or.inl h2a
  have h2:x ∈ B ∧ x ∈ C:= And.intro h1b h2b
  exact Or.inr h2
