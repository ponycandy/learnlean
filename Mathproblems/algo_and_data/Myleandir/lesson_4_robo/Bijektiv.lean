
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Init.Logic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
open Function
example : let f := fun (n : ℤ) ↦ n + 1 ;
Function.Bijective f := by
{
  unfold Function.Bijective
  constructor
  intro a1 a2 hab
  simp at hab
  tauto
  unfold Function.Surjective
  intro b
  use b-1
  simp
}
example {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
{
  apply Iff.intro
  intro h1
  obtain ⟨finj, fsurj⟩  := h1
  choose g hg using fsurj
  have hR : RightInverse g f := by
  {
    exact hg
  }
  use g
  constructor
  dsimp [Function.RightInverse]
  apply rightInverse_of_injective_of_leftInverse finj
  unfold Function.RightInverse at hR
  assumption
  assumption
  intro h1
  choose g hg using h1
  cases' hg with hg1 hg2
  unfold Bijective
}
example : (Fin 3 → A) ≃ A × A × A := by
{
  --从纯计算机角度看，
  --这就是一个equiv structure的定义赋值过程
  fconstructor
  --所以，上面这个tactic的作用是使得命题形式为structure赋值过程的命题自动分裂到每个成员里面
  exact fun f => (f 0, f 1, f 1)
  exact fun t => fun
    | 0 => t.1
    | 1 => t.2.1
    | 2 => t.2.2
}
example (f : A ≃ B) : Bijective f.toFun := by
{
  constructor
  intro a1 a2 h
  simpa [congr_arg f.invFun] using h
}
