import Mathlib.Analysis.Analytic.Basic
import Mathlib.Init.Logic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
example :let f := fun (n : ℤ) ↦ n + 3;
    Function.Injective f := by
{
  unfold Function.Injective
  intro fc b
  intro b1
  intro hyp
  simp  [fc] at hyp
  assumption
}

example : let f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1;
    ¬ Function.Injective (f + f) := by
{
  unfold Function.Injective
  push_neg
  simp
  use 2
  use 3
  tauto
}
example {f : A → B} (hf : Function.Injective f)
    {b : B} (hb : b ∈ Set.range f) :
    ∃! a, f a = b := by
{
  --存在唯一的a,目前还不知道使用什么策略去展开
  -- unfold Set.range at *
  -- obtain ⟨ s,hs⟩ := hb
  --上面两句话可以用下面的话取代，相当于一个长逻辑链的自动推导
 rcases hb with ⟨a, ha⟩
 --我们更喜欢先展开定义然后再使用各种Tactic，
 --我们的逻辑连接没有这么长（大脑缓存的数据链节点有限）
 use a
 constructor
 simp
 assumption
 intro y
 intro h1
 rw[← ha] at h1
 apply hf
 assumption
--  rw[← hf] at h1
}
example {A B : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    (hf : StrictMono f)  : Function.Injective f := by
{
  intro a b--会自动展开目标中的\exist量词
  intro h1
  rcases lt_trichotomy a b with hlt | heq | hgt
  apply hf at hlt
  rw [h1] at hlt
  simp at *
  assumption
  apply hf at hgt
  rw [h1] at hgt
  simp at *
}
example:
let f := fun (n : ℤ) ↦ n^3 + (n + 3);
Function.Injective f := by
{
  apply StrictMono.injective
  apply StrictMono.add
  apply Odd.strictMono_pow
  trivial
  intro a b
  simp
}
example :Function.HasLeftInverse Nat.succ  := by
{
  use Nat.pred
  unfold Function.LeftInverse
  simp
}
example {A : Type*} [Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
{
  let g : ℤ → A := fun
    | Int.ofNat n => f n
    | Int.negSucc _ => Classical.arbitrary A
    --相当于用if else定义函数
  use g
  simp
}
example {f : A → B} {g : B → A} (hL : Function.LeftInverse g f)
    (S : Set A) :
    f '' S ⊆ g ⁻¹' S := by
{
  intro b
  intro hb
 -- unfold Set.image
  obtain ⟨x, hx, e⟩ := hb--why?
  --obtain相当于连续使用intro和rcases将假说分解为最小单元,<>里面的元素数量
--就是分解操作的执行次数。obtain本质上自动化了多次引入
  dsimp [Function.LeftInverse] at hL
  rw [← hL x, e] at hx
  apply hx
}
example {f : α → β} (h : Function.HasLeftInverse f) :
    Function.Injective f := by
{
  rcases h with ⟨finv, inv⟩
  intro a b eq
  trans finv (f a)
  rw [inv]
  rw [eq]
  rw [inv]


}
