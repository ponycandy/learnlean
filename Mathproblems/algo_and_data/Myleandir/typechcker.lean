import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Subfield

def hello := "world"
#eval "hello world"
def yuansu : Nat := 1
def C : Type := Prop
def I : Type := Prop
def S : Type := Prop

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat


--#check λ h : C => C
--#check fun h : C => C
--注意，冒号右侧的东西是用来说明输入类型的，=>表示的是输出
--h: I ∧ S 描述的是输入的格式，但是直接写是计算不了类型的,如下所示
--#check fun h: I ∧ S => And.intro h.right h.left
--正确的写法是:
#check fun h:Prop => h

#check fun h => And.intro h h

#check fun x => x + 5
#check fun x : Nat => true

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
def double (x : Nat) : Nat :=x + x
