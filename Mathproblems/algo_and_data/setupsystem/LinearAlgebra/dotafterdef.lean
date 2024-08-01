import Mathlib.Data.Nat.Cast.Basic
def some_mapper(x:α):α:=x
def funconmapper(x :α ):α:=x

variable(x:α )
open Nat
#check funconmapper (some_mapper (x))
#check (some_mapper (x)).funconmapper
#check succ (1)
#eval succ (1)
variable(y:Nat)
--the following two experssion is equiv
#check succ (y)
#check y.succ
--therefore, XX.somefunc _ _ is equiv to
--somefunc XX _ _
--here comes more samples
def AdduptwoNat(x:Nat)(y:Nat):Nat:= x+y
variable (z:Nat)
#check AdduptwoNat y z
#check z.AdduptwoNat y --wow,seemed wrong
--turns out they should be defined under the same namespace
def Nat.AdduptwoNat(x:Nat)(y:Nat):Nat:= x+y
variable (z:Nat)
#check Nat.AdduptwoNat y z
#check z.AdduptwoNat y
--so it is clear ,the reason why we can use
--Matrix.map is that it is equiv to map Matrix _ _
--and same for anyother function!
