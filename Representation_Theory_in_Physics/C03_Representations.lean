import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Real.Basic

open Matrix
-- variable (G:Type) [Group G] -- assume G

-- The following "section" builds the group of two elements.

inductive mySet where
| my_one : mySet
| my_two : mySet

open mySet

#check my_one -- notice how mySet.my_one is the "right" way to call my_one. That's why it's useful to "open" mySet above.

def mySet_mul : mySet → mySet → mySet := by
  intro h1 h2
  match h1 with
  | my_one =>
      match h2 with
        | my_one =>
             exact my_one
        | my_two =>
             exact my_two
  | my_two =>
       match h2 with
        | my_one =>
             exact my_two
        | my_two =>
             exact my_one

--def mySet_mul2 : mySet → mySet → mySet
--| my_one my_one => my_one
--| my_one my_two => my_two
--| my_two my_one => my_two
--| my_two my_two => my_one -- pattern matching recursive function

instance : Group mySet where

  mul:= mySet_mul
  one:= my_one
  inv:= by
    intro h1
    match h1 with
      | my_one =>
          exact my_one
      | my_two =>
          exact my_two
  mul_one := by
    intro a
    match a with
      | my_one =>
          unfold OfNat.ofNat
          unfold One.toOfNat1
          simp
          unfold HMul.hMul instHMul
          simp
          rw [mySet_mul]
      | my_two =>
          unfold OfNat.ofNat
          unfold One.toOfNat1
          simp
          unfold HMul.hMul instHMul
          simp
          rw [mySet_mul]
  mul_assoc := by
    intro a b c
    match a with
      | my_one =>
        match b with
          | my_one =>
            match c with
              | my_one =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul]
              | my_two =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
          | my_two =>
            match c with
              | my_one =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
              | my_two =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
      | my_two =>
        match b with
          | my_one =>
            match c with
              | my_one =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
              | my_two =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
          | my_two =>
            match c with
              | my_one =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
              | my_two =>
                unfold HMul.hMul instHMul
                simp
                rw [mySet_mul, mySet_mul, mySet_mul]
  one_mul:= by
    intro a
    match a with
      |my_one =>
        unfold HMul.hMul instHMul
        simp
        unfold OfNat.ofNat
        unfold One.toOfNat1
        simp
        rw [mySet_mul]
      |my_two =>
        unfold HMul.hMul instHMul
        simp
        unfold OfNat.ofNat
        unfold One.toOfNat1
        simp
        rw [mySet_mul]
  inv_mul_cancel:= by
    intro a
    match a with
      | my_one =>
        unfold Inv.inv
        simp
        unfold OfNat.ofNat One.toOfNat1
        simp
        unfold HMul.hMul instHMul
        simp
        rw [mySet_mul]
      | my_two =>
        unfold Inv.inv
        simp
        unfold OfNat.ofNat One.toOfNat1
        simp
        unfold HMul.hMul instHMul
        simp
        rw [mySet_mul]

-- ayyyyy we have a group now!
-- as an aside, proving mul_assoc is kindof comical. It would grow very quickly. Here we have to match over the 2^{3} = 8 possible instances of a b c. Is there a  concise way to write

#check Group mySet

-- now we can start defining representations!

variable (G:Type) [Group G] -- assume G

def representation (n:ℕ) := G → GeneralLinearGroup (Fin n) ℝ -- for now we assume our representations are over the reals...

-- we can use this definition to build representations from Group mySet → GL_{n}(R).
