import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic


example (P C: Prop)(p: P)(bakery_service : P → C) : C := by
{
  #check bakery_service
  exact bakery_service p
}

example (C: Prop) : C → C := by
{
  tauto
}
example (I S: Prop) : I ∧ S → S ∧ I := by
{
  exact fun h : I ∧ S ↦ ⟨h.right ,h.left⟩
}

example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
{
  intros HC HD -- Introduce assumptions for C and D
  apply h -- Apply hypothesis h : C ∧ D → S
  exact ⟨HC, HD⟩ -- Show that C ∧ D implies S
}
example (C D S: Prop) (h : C → D → S) : C ∧ D → S := by
{
  intro HC
  have h1: C := HC.left
  have h2 : D := HC.right
  have h3: D → S := h h1
  exact h3 h2
}
example (C D S : Prop) (h : (S → C) ∧ (S → D)) : S → C ∧ D := by
{
  intro hs
  have h1: S → C := h.left
  have h2: S → D := h.right
  have hc:= h1 hs
  have hd:= h2 hs
  exact ⟨ hc,hd⟩
}
example (R S : Prop) : R → (S → R) ∧ (¬S → R) := by
{
  intro hR
  have h1: S → R :=by
    intro Hs
    exact hR
  have h2:¬S → R:=by
    intro HS
    exact hR
  exact ⟨ h1,h2⟩
}
example (P Q : Prop)(h'₁ : P)(h'₂ : Q) : P ∧ Q := by
{
  constructor
  assumption
  assumption
}
example (P Q R S : Prop)(h'₁ : P)(h'₂ : Q)(h'₃ : R)(h'₄ : S) : (P ∧ Q) ∧ R ∧ S := by
{
  constructor
  constructor
  assumption
  assumption
  constructor
  assumption
  assumption
}
example (P Q : Prop)(h: P ∧ Q) : P := by
{
  cases h
  assumption
}
example (P Q R: Prop) (h : P → Q → R) : P ∧ Q → R := by
{
  intro hpq
  apply h
  cases hpq
  assumption
  cases hpq
  assumption
  --这里注意，多个\r符号的apply，会转换的子目标是前面所有的子项目都是true
}
example (O S : Prop)(s : S) : S ∨ O := by
{
  exact Or.inl s
}
example (B C I : Prop)(h1 : C → B)(h2 : I → B)(h3 : C ∨ I) : B := by
{
  exact Or.elim h3 h1 h2
}

example (C O : Prop)(h : C ∨ O) : O ∨ C := by
{
  #check Or.elim h Or.inr Or.inl
  exact Or.elim h Or.inr Or.inl
}
example (I K P : Prop)(h : K → P) : K ∨ I → I ∨ P := by
{
  intro h1
  cases' h1 with h1a h1b
  exact Or.inr (h h1a)
  exact Or.inl h1b
}

example : ¬False := by
{
  exact False.elim
  --证明一个命题为False的方法：
-- example : False :=
-- false.elim
}
example (B S : Prop)(h : ¬S) : S → B := by
{
  --注意这个命题和前面的显然不一样的地方，
  --那就是这个命题是假命题
  --任务是证明为假命题
-- You've made use of the concept that "false implies anything".
-- h           : S     → False
-- false_elim  : False → B
-- Because the righthand side of h and the lefthand side of false_elim match, you can use imp_trans to combine these:
-- imp_trans h false_elim
  #check ¬S
  #check S     → False
  #check λs ↦ False.elim (h s)
  #check S → B
  --还是看不懂lambuda的用法，fun也看不懂
  --请把/not S当作S ->flase来用
  exact λs ↦ False.elim (h s)
  --无法check，因为匿名函数无法使用任何变量名称引用
  --下面是第二种写法False imply anythin关键点
  -- intro hs
  -- have h3: False := h hs
  -- exact false_elim h3

}

-- 使用fun关键字定义一个匿名函数，计算一个数的平方
def twice (f : Nat -> Nat) (x : Nat) : Nat :=
  f (f x)

#eval twice (fun x => x + 1) 3
--可见fun定义了一个类型为Nat -> Nat的对象
#eval twice (fun (x : Nat) => x * 2) 3

example (P : Prop)(p : P) : ¬¬P := by
{
  --记住，¬P表示 P->false
  --当定理的输入为多个assumption的时候
  --，apply 定理将会将原本的输入变为输出
  apply imp_trans
  intro h
  have h1 := h p
  exact false_elim h1
  intro h1
  exact h1
}

example (L : Prop) : ¬(L ∧ ¬L) := by
{
  apply imp_trans
  intro
  have h1:= a.right
  have : False := h1 a.left
  exact this
  exact identity
}
example (B P : Prop) (h : B ↔ ¬P) : (B → ¬P) ∧ (¬P → B) := by
{
  have h1:= iff_mp h
  have h2:= iff_mpr h
  exact ⟨ h1,h2⟩

}
example (P Q R : Prop) (h1 : P ↔ R)(h2 : P → Q) : R → Q := by
{
  have h1a:= h1.mpr
  exact imp_trans h1a h2
}
example (P Q R : Prop): (P ∧ Q ↔ R ∧ Q) ↔ Q → (P ↔ R) := by
{
  apply iff_intro
  intro
  intro
  apply iff_intro
  intro
  have a3:P ∧ Q := ⟨ a_2,a_1⟩
  have h4:R ∧ Q := iff_mp a a3
  exact h4.left
  intro
  have a3:R ∧ Q := ⟨ a_2,a_1⟩
  have h2: P ∧ Q := iff_mpr a a3
  exact h2.left
  intro
  apply iff_intro
  intro
  have h1:P ↔ R := a a_1.right
  have h4: R := iff_mp h1 a_1.left
  exact ⟨ h4,a_1.right⟩
  intro
  have h4:P ↔ R := a a_1.right
  have h2: P := iff_mpr h4 a_1.left
  exact ⟨ h2,a_1.right⟩
}
example (P Q : Prop)(h'₁ : P) : P ∨ Q := by
{
  left
  assumption
}
example (P Q : Prop)(h'₁ : ¬P) : P → Q := by
{
  intro
  contradiction
}
example (P Q : Prop) (h: Q) : ¬(¬Q ∧ P) := by
{
  intro ⟨nq, p⟩
  --这里涉及到编程语言中的pattern match，我们会在下面说明
  --由于目标是¬Q ∧ P ->false，所以，如果能够存在一个形如
  -- ¬Q 和P的假设，那么<¬Q,P>的形式就可以证明结论。
  -- 所以，引入的假设就具备这个形式：⟨nq, p⟩
  have h1:False := nq h
  assumption
}
--https://lean-lang.org/functional_programming_in_lean/getting-to-know/datatypes-and-patterns.html
