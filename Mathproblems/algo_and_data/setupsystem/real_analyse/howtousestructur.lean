structure Point where
  x : Float
  y : Float
deriving Repr
--for example ,I can use a structur this way
def origin : Point := { x := 0.0, y := 0.0 }
#check origin
#check origin.x
#check origin.y

--so structur define a type
