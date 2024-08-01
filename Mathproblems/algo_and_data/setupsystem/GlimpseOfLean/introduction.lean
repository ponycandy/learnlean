import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Complex.Exponential
--这里的练习就很简单，不涉及到范畴论的多层嵌套
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε
--所以我们发现，可以不借助mathlib的系统建立极限的概念
--这也是我们今后将会采取的途径，

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by
{
  unfold seq_limit at *
  unfold continuous_at at *
  intro ε hε
  #check hf ε hε
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  use N
  intro n hn
  apply Hf
  exact Hu n hn
}

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
}

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  ring
}
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
}
example (a b c d : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h, h']
  ring
}
example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by {
  rw[h,h',h]
  ring
}
open Real
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add (a + b) c]
  rw [exp_add a b]
}

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by {
  rw[exp_sub]
  rw[exp_zero]
  rw[mul_one]
  rw[exp_add]
}

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring
}

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by {
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by rw[h]
              _ = exp ((b + b) + (c + c))           := by ring
              _ = exp (b + b) * exp (c + c)         := by rw[exp_add]
              _ = (exp b * exp b) * (exp c * exp c) := by repeat rw[exp_add]
              _ = (exp b) ^ 2 * (exp c)^2           := by ring
}
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by {
  exact sq_pos_of_pos ha
}
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a^2`
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha -- this is exactly our assumption `ha`.
}

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  apply add_pos
  exact sq_pos_of_pos ha
  exact sq_pos_of_pos hb
}

example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by {
  intro h1 h2
  intro ptrue
  #check h2 ptrue (h1 ptrue)
  exact h2 ptrue (h1 ptrue)
}

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl
}
