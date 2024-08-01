import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Cardinality
import Mathlib.Algebra.Order.Algebra
import Mathlib.Tactic.Linarith
--sample of a floor ring
universe U
#check Nat
#check FloorRing
#check FloorRing (ℕ:Type)
--see the defination of linear_ordered_ring
--the property: zero:α is not satisfied
#check FloorRing ℤ
#check Int.floor (1:ℤ)
--
#check Int.floor (2:ℤ)
--this definition is not suitable for my problem
--I need a floor function over ℝ
#check LinearOrder ℝ
--Is there an Instance of LinearOrder ℝ?
--Is there a way to find it?
#check  Int.floor (1.5:ℝ)
#check  FloorRing ℝ
-- variable(tempfloorring :FloorRing ℝ)
--if FloorRing is a structure,then clearly we can use
--its member to calc something
-- however,it is not possible to write down the constructor
#check tempfloorring.floor
#check tempfloorring.floor 3
--the structure is seen as a type
--although it is not possible to construct it using mk
--we can just define its type and use the member
#check tempfloorring.floor 3.1

theorem lt_to_gt (a b : ℝ) (h : a < b) : b > a :=
{
  lt_trans h (lt_irrefl a)
}
example :tempfloorring.floor 3.1=3:= by
{
  simp

  --it is harder than I thought.......
  --can't unfold the definition here...
  -- #check ⌊(3.1:ℝ )⌋
  have h1:⌊(3.1:ℝ )⌋ ≤  (3.1:ℝ)  := by
  {
    apply Int.floor_le
     -- rw[tempfloorring.gc_coe_floor]
      --simp
      --part of a structure
      --or member of a structure can be used as
      --a theroem or a lemma
  }

  -- have h2 : 2  <⌊(3.1:ℝ )⌋  := by
  -- {
  --  --   apply Int.sub_one_lt_floor
  --   have temp:= Int.sub_one_lt_floor (3.1:ℝ)
  --   have temp_1:(2:ℝ )<((3.1-1 ):ℝ ):= by
  --   {
  --     --linarith
  --     --this is a calculation
  --     ring_nf
  --     ring
  --     --when concered with calculation on ℝ
  --     --it become difficult to use.....
  --     --it look like a proof ,but it is actually a calc
  --     linarith
  --     --I don't know why this tactic work here but not the begining.....
  --     -- I guess we can see ring as some sorts of calculation?
  --   }
  --   --rw [Int.sub_one_lt_floor (3.1:ℝ)]
  --   --how to handle theroem with implicit input?
  --   --1.one way is to do Type conversion by adding colon
  --   --2.another way is to use placeholder _
  --   --also,use a filed name (like Int.) to lock the type
  --   --one corner case of my logic is that
  --   -- I don't remeber to think like a machine!
  --   #check gt_trans temp temp_1
  --   have temp3 := gt_trans temp temp_1

  -- }
--so even if we have proven this example
--we can't use this directly
  rw[Int.floor_eq_iff]
  constructor
  --prove that ↑3 ≤ 3.1
  --remember that order only exist on the same algebra ring
  --any compare should be convert to the same ring first
  ring_nf
  linarith
  --same
  ring
  linarith
}
--so this is how we use floor function
--we first define a floor ring over ℝ
--which is a structru
-- than we can use the theroem or definition
--of floor(gc_coe_floor) of that structure!
--this is also how a strucutr or a class can be used in
--lean prover!

--for compare over numbers. convert them to the same ring first!
--an instance of FloorRing ℝ
-- instance : FloorRing ℝ  where
--   floor := id
--   ceil := id
--   gc_coe_floor a b := by
--     rw [Int.cast_id]
--     rfl
--   gc_ceil_coe a b := by
--     rw [Int.cast_id]
--     rfl
--How do I know whether instance: FloorRing ℝ
--has been defined or Not?
--class almost always need to used with Instance
-- https://stackoverflow.com/questions/74976596/go-to-type-class-instance-definition-in-lean-4
#synth Inhabited Nat
#check instInhabitedNat
#synth FloorRing ℤ
#check instFloorRingInt
--Yuh,it work
#synth FloorRing ℝ
#check Real.instFloorRing
--proved to be noncomputable
--now wonder I can'tget 3 out of ⌊(3.1:ℝ )⌋
--it's like 2^0.5,in ancient time,people don't
--know how to get the value of 2^0.5(1.414...)
--so it can only be represent that way.
--therefore, floorRing is noncomputable in lean
