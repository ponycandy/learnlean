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

-- theorem compl_compl (A : Set U) : Aᶜᶜ = A := by
--   apply Subset.antisymm
--   intro x
--   intro h1
--   rw[mem_compl_iff] at h1
--   rw[mem_compl_iff] at h1
--   push_neg at h1
--   exact h1
--   intro x1
--   intro h1
--   by_contra h2
--   rw[mem_compl_iff] at h2
--   push_neg at h2
--   rw[mem_compl_iff] at h2
--   exact h2 h1

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  intro h1
  exact Set.compl_subset_compl_of_subset h1
  --如果theroem中包含了{h:XX}前提,则不能够使用rw策略
  --因为此时theroem中只包含h假说,此时使用exact策略会将前提推向结论
  --注意set theory中的语法，包含了{h:XX}前提时,直接用theroem h可以直接
  --从theroem中的h推导到结论，从而生成新的assumption
  intro h1
  have h2 : Aᶜᶜ ⊆ Bᶜᶜ := compl_subset_compl_of_subset h1
  rw[compl_compl] at h2
  rw[compl_compl] at h2
  exact h2


example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x
  intro h
  have hAC : x ∈ (A ∪ C) := by--子定理使用by:可以设置中间目标
    rw[Set.mem_union]
    exact Or.inl h
  have h3: x ∈ B ∪ C :=  h1 hAC
  cases' h3 with h3a h3b
  exact h3a
  have h4:x ∈ A ∧  x ∈ C := And.intro h h3b
  rw[← Set.mem_inter_iff] at h4
  have h5:x ∈ B ∩ C := h2 h4
  exact h5.left
