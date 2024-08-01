
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic
--下面现实fun的用法,函数是可以视作assumption的
example (C: Prop) : C → C := by
  have h : C → C := fun C => C
  exact h
--下面是第二种写法
--exact fun C => C
example (I S: Prop) : I ∧ S → S ∧ I := by
--fun 格式相当于定义一个新的assumption类型为prop。输入不直接指明
  exact fun h: I ∧ S => And.intro h.right h.left
--注意，冒号右侧的东西是用来说明输入类型的，=>表示的是输出
--h: I ∧ S 描述的是输入的格式，但是直接写是计算不了类型的,如下所示
--#check fun h: I ∧ S => And.intro h.right h.left
--正确的写法是:


-- example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
--   exact imp_trans h1 h2

-- example (P Q R S T U: Prop) (p : P) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : U := by
--   exact (h1 ≫  h3 ≫ h5) p
structure Point where
  x : Float
  y : Float
deriving Repr
def sample : Point :=  { x := 0.0, y := 0.0 }
#eval sample

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

example (x : ℝ )(f : ℝ → ℝ ): ∃ α :ℝ , f (x)=α  := by
{
  use f x
}--need to practivve on real number!
--可能存在其它的做等量代换的函数
--但是如果我们假设我们是从0开始搭建tactic和therom框架的，
--上面这个等量代换的theroem就是可用的！

-- exact ⟨⟨a,i⟩,⟨o,u⟩⟩
