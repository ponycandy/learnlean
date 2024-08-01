import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield

example (A : Set U) : ∃ s, s ⊆ A := by
  have h : A ⊆ A := Set.Subset.refl A
  #check h
  exact Exists.intro A h

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x
  intro h2
  rw[Set.mem_sUnion]
  apply Exists.intro A
  exact And.intro h1 h2


example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x
  intro h2
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion] at h2
  obtain ⟨s, hs⟩ := h2
  use s
  have h2: s ∈ G := h1 hs.left
  exact And.intro h2 hs.right

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  apply Subset.antisymm
  intro x h
  rw[mem_sUnion]
  rw[mem_union] at h
  cases' h with h1 h2
  use A
  have h2 :A ∈ {A, B}
  rw[mem_pair]
  have h2 : A=A :=rfl
  exact Or.inl h2
  exact And.intro h2 h1
  use B
  have h3 :B ∈ {A, B}
  rw[mem_pair]
  have h3 :B=B:=rfl
  exact Or.inr h3
  exact And.intro h3 h2
  intro x h
  rw[mem_sUnion] at h
  obtain⟨s,hs⟩  := h
  have hs1 : s ∈ {A, B} := hs.left
  have hs2 : x ∈ s := hs.right
  rw[mem_pair] at hs1
  cases' hs1 with hsa hsb
  rw[hsa] at hs2
  rw[mem_union]
  exact Or.inl hs2
  rw[hsb] at hs2
  rw[mem_union]
  exact Or.inr hs2
