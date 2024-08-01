
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def double (x : Nat) := 2*x
def triple (x : Nat) := 3*x

#check compose Nat Nat Nat double triple 10 -- Nat
#eval  compose Nat Nat Nat double triple 10 -- 60

def appendWorld (s : String) := s ++ "world"
#check String.length -- String → Nat

#check compose String String Nat String.length appendWorld "hello" -- Nat
#eval  compose String String Nat String.length appendWorld "hello" -- 10

#check compose _ _ _ double triple 10 -- Nat
#eval  compose Nat Nat Nat double triple 10 -- 60
#check compose _ _ _ String.length appendWorld "hello" -- Nat
#eval  compose _ _ _ String.length appendWorld "hello" -- 10

def Implicit_compose {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
#check Implicit_compose double triple 10 -- Nat
#eval  Implicit_compose double triple 10 -- 60
#check Implicit_compose String.length appendWorld "hello" -- Nat
#eval  Implicit_compose String.length appendWorld "hello" -- 10
