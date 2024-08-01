import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
open Matrix

section generatematrix
#check Matrix ℕ ℕ ℕ
#check Matrix (Fin 3) (Fin 3) ℕ

example(M1: Matrix (Fin 3) (Fin 3) ℕ) (M2: Matrix (Fin 3) (Fin 3) ℕ)
(h: (∀ i j : (Fin 3), M1 i j = M2 i j)): M1=M2 := by
{
  rw[ext_iff] at h
  assumption
}

variable(testfunctrans:ℕ → ℕ → ℕ)
#check of testfunctrans
variable(testfunctrans1:ℝ  → ℝ  → ℝ  )
#check of testfunctrans1
#check of.symm testfunctrans1
#check (Equiv.symm of) testfunctrans1
--why can of.symm be used? where is member .symm defined?
--when are we allowed to use .XX of a theroem
--or when are we allowed to use .XX of a subject
--the anwser is simple: whnever we feel like it....

end generatematrix
section mappdohere
def funcOnMatrix (x:ℕ ): ℕ  → ℕ  :=10*x
def testfunctrans (x y:Fin 3 ):Fin 3 → Fin 3 → ℕ:=x+y
#check funcOnMatrix
#check of testfunctrans
--desired type is Matrix Fin3 Fin3 ℕ
--but got Matrix (Fin 3) (Fin 3) (Fin 3 → Fin 3 → ℕ)
--instead.we can  verify how type conversion work here
--check the definition of "≃": a two side function of
-- α → β,so iw would be (m → n → α) → (Matrix m n α)
--as Matrix is a Fin 3 → Fin 3 → ℕ,it make perfect sense
--variable(M1:Matrix (Fin 3) (Fin 3) ℕ)
#check (M2: of testfunctrans)

--I can't "assign" the value "of testfunctrans"
--directly to another variable
--but using of testfunctrans directly in map is fine
#check map M1 funcOnMatrix
#check map (of testfunctrans) funcOnMatrix
--lean don't seem to care about instaneation of
--a matrix like M1,it only care about that it is
--a certain form of matrix

def funcOnMatrix_modified (x: (Fin 3 → Fin 3 → ℕ)): ℕ  → ℕ  :=1
#check map (of testfunctrans) funcOnMatrix_modified
--so this work.we need to machanically follow the instruction
example (M:Matrix (Fin 3) (Fin 3) ℕ )(f:ℕ → ℕ )(i:Fin 3)(j: Fin 3)
: M.map f i j = f (M i j):= by
{
  exact map_apply
}
--why can I do .map afer M here?M is not a structure after all
--same why can I do of.symm here? of is also not a structure
-- first question,why can I .symm after of?
-- in object oriented language,a colon usually means:
-- namespace,or,member of a class
-- clearly it is not a namespace issue here
-- so it must be a member of class
--but Equiv.relf is a member of "of",and symm is the member of Equiv.relf
-- any object after := is a member of that object
-- therefore can be used by colon
--so it is clear ,the reason why we can use
--Matrix.map is that it is equiv to map Matrix _ _
--and same for anyother function!
end mappdohere
section continueonmatrix
example(M1:Matrix (Fin 3) (Fin 3) ℕ ) :M1.map id=M1:=by
{
  apply map_id
}

variable(M1:Matrix (Fin 3) (Fin 3) ℕ )
#check transpose M1
#check M1ᵀ
#check conjTranspose M1
variable (M2:Matrix (Fin 5) (Fin 3) ℕ )
#check transpose M2
#check conjTranspose M2 --map a "star" operation after transpose
--interseting thing is what makes up a star operation?
--
end continueonmatrix
section understand_instance_and_ingabited_and_otherthings
--https://subfish-zhou.github.io/theorem_proving_in_lean4_zh_CN/type_classes.html
--instance概念最更本的东西是typeclasses即类型类
-- 这是一个有点脱裤子放屁的东西
-- 但是我们可以先从Object Oriented语言为基础出发去理解
--https://medium.com/@olxc/type-classes-explained-a9767f64ed2c

--我们给出instance的推导过程
--Typeclasses:
--Here is an example in Lean to demonstrate
--the basic idea of Type classes:

-- Define a type class called "has_add" for types that support addition
class has_add (α : Type) :=
(addsup : α → α → α)
class has_bi_ops (α :Type) :=
  addsup : α → α → α
  prodsup : α → α → α
-- Create an instance of the type class
-- for the type nat (natural numbers)
-- with the addition operation
instance : has_add Nat :=
{ addsup := Nat.add }
instance : has_bi_ops ℕ:=
  {addsup := Nat.add,prodsup:=Nat.add}

-- Define a function that uses the "has_add"
-- type class constraint
def add_two {α : Type} [inst:has_add α] (a : α) : α
:=inst.addsup a a

-- Test the function with natural numbers
#eval add_two 3 -- Output: 6
--In this example, we define a type class
-- has_add for types that support addition.
-- We create an instance of this type class
--for the type nat (natural numbers) with
--the addition operation. Then,
--we define a function add_two that
-- takes any type α that has an instance
--of the has_add type class and adds the
--input value to itself.
--Finally, we test the function with
--natural numbers and evaluate the result.
--second example here:

class customAdd (a : Type) where
  addups : a -> a -> a
def double [customAdd a] (x : a) : a
:= customAdd.addups (customAdd.addups x x) x

instance : customAdd Nat where
  addups := Nat.add
#check @double--got 1 implicit input
#check double 3--it only check type here
#eval double 3--this is whre it does calculation
--now let's find the star instance on ℕ :
variable (M2:Matrix (Fin 5) (Fin 3) ℕ )
#check conjTranspose M2
#check Star ℕ
#check Star ℝ
def someop{a:Star ℝ}(x:ℝ ):=a.star x--Hmmm..
---seemed not working,star is never instanite
#check someop 1
--you can see floor ring as good sample for understanding
--Type classes
#print inferInstance
end understand_instance_and_ingabited_and_otherthings
section operationdefinition
-- variable (M1:Matrix (Fin 5) (Fin 3) ℕ )
-- variable (M2:Matrix (Fin 3) (Fin 5) ℕ )
-- variable (M3:Matrix (Fin 3) (Fin 3) ℕ )
#eval (Inhabited.default : Matrix (Fin 3) (Fin 3) ℝ )
#check Inhabited (Matrix ℕ  ℕ  ℝ)
#check DecidableEq (Matrix ℕ ℕ ℝ )
#check Fintype (Matrix (Fin 3) ℕ  ℝ )
#check Add (Matrix (Fin 3) (Fin 3)  ℝ)
def add_two_Matrix [inst:Add (Matrix (Fin 5) (Fin 3) ℕ )]
 (a : Matrix (Fin 5) (Fin 3) ℕ )
  (b:Matrix (Fin 5) (Fin 3) ℕ  ):
 Matrix (Fin 5) (Fin 3) ℕ:=inst.add a b
 #check add_two_Matrix M1 M1 --Typecheck is OK
 --#eval add_two_Matrix M1 M1 --but evaluation is still not possible
 --It is actually the same pattern as before,the only diff
 --is the Type cheking
 --class-instance-deffunc,but it can't be evaluate
--because inst does not have any subject that we can de-string on
--不行，封包层次过高了。深入不到下面，我们跳过this instance往后吧
--let's check whether Add is istance for R
#check Add ℝ
#check Real.instAdd --this is Add ℝ
#eval (1:ℝ )+(1:ℝ )--lean4 can't do calculation....
#eval 1+1
--how about that:in matrix proof
--we only focus on the matrix,not the real number
--therefore, the only thing that matter is knowing
--that the operation of "instance Add" exist
--for not just the real number
--but all universal types,therefore,eval migth not be possible
section goontheroem
-- variable (M1:Matrix (Fin 5) (Fin 3) ℕ )
-- variable (M2:Matrix (Fin 3) (Fin 5) ℕ )
-- variable (M3:Matrix (Fin 3) (Fin 3) ℕ )
#check (0: (Matrix (Fin 3) (Fin 3) ℕ))--
--0 is a subject of Objectset,and have been bind with Type Matrix (Fin 3) (Fin 3) ℕ
example (i:Fin 3)(j: Fin 3)(mx: (Matrix (Fin 3) (Fin 3) ℕ):=0): mx i j=0:= by
{
 -- rfl--some unknown
  rw[zero_apply]
}
example (A B : Matrix ℕ  ℕ  ℝ ) (i : ℕ ) (j : ℕ ) :
    (A + B) i j = (A i j) + (B i j) := by
{
  --Type checker does very long job of type check and verify
  apply add_apply
}
example : of (0 : ℕ  → ℕ  → ℝ ) = 0:= by
{
  #check of (0 : ℕ  → ℕ  → ℝ )
  apply of_zero
  --so when a subject is defined,we always
  --first define its Ring or group property
}
end goontheroem
section startdiagnal
def test_diagfunc (x:Fin 3 ):Fin 3 → ℝ :=x
#check ( diagonal (test_diagfunc))
--our habit is to give the value above to some variable else...
#check((diagonal (test_diagfunc)) 1 1)
--again,eval will not work, and results is not computable
#eval ((diagonal (test_diagfunc)) 1 1)


end startdiagnal
