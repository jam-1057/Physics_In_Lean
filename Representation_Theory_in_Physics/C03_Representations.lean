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
-- as an aside, proving mul_assoc is kindof comical. It would grow very quickly. Here we have to match over the
-- 2^{3} = 8 possible instances of a b c. Is there a  concise way to write

-- now we can start defining representations!

-- assume G

def representation (G:Type) [Group G] (n:ℕ) := G →* GeneralLinearGroup (Fin n) ℝ -- for now we assume our representations are over the reals...

-- we can use this definition to build representations from Group mySet → GL_{n}(R).

def mySet_trivialMap : mySet → GeneralLinearGroup (Fin 1) ℝ  := by
  intro g
  match g with
    | my_one =>
      exact 1
    | my_two =>
      exact 1

instance : MulHom mySet (GeneralLinearGroup (Fin 1) ℝ) where
  toFun := mySet_trivialMap
  map_mul' := by
    intro x y
    match x with
     | my_one =>
        match y with
          | my_one =>
            rw [mySet_trivialMap]
            have h: (my_one * my_one = my_one) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_one) (my_one) -- I found this by trial and error, lean suggestions were helpful here.
            rw [h]
            rw [mySet_trivialMap]
            simp
          | my_two =>
            rw [mySet_trivialMap, mySet_trivialMap]
            have h: (my_one * my_two = my_two) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_one) (my_two)
            rw [h]
            rw [mySet_trivialMap]
            simp
     | my_two =>
        match y with
          | my_one =>
            rw [mySet_trivialMap, mySet_trivialMap]
            have h: (my_two * my_one = my_two) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_two) (my_one)
            rw [h]
            rw [mySet_trivialMap]
            simp
          | my_two =>
            rw [mySet_trivialMap]
            have h: (my_two * my_two = my_one) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_two) (my_two)
            rw [h]
            rw [mySet_trivialMap]
            simp

-- nice. We have shown that mySet_trivialMap, which takes mySet and maps it to GL(1, Reals) is a homomorphism!

-- there is one more irreducible representation that maps the identity to the identity and the other element to negative one. Let's define it:

def mySet_MapTwo : mySet → GeneralLinearGroup (Fin 1) ℝ  := by
  intro g
  match g with
    | my_one =>
      exact 1
    | my_two =>
      exact -1

instance : MulHom mySet (GeneralLinearGroup (Fin 1) ℝ) where
  toFun := mySet_MapTwo
  map_mul' := by
    intro x y
    match x with
     | my_one =>
        match y with
          | my_one =>
            rw [mySet_MapTwo]
            have h: (my_one * my_one = my_one) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_one) (my_one) -- I found this by trial and error, lean suggestions were helpful here.
            rw [h]
            rw [mySet_MapTwo]
            simp
          | my_two =>
            rw [mySet_MapTwo, mySet_MapTwo]
            have h: (my_one * my_two = my_two) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_one) (my_two)
            rw [h]
            rw [mySet_MapTwo]
            simp
     | my_two =>
        match y with
          | my_one =>
            rw [mySet_MapTwo, mySet_MapTwo]
            have h: (my_two * my_one = my_two) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_two) (my_one)
            rw [h]
            rw [mySet_MapTwo]
            simp
          | my_two =>
            rw [mySet_MapTwo]
            have h: (my_two * my_two = my_one) := by
              unfold HMul.hMul instHMul
              simp
              exact mySet_mul.eq_def (my_two) (my_two)
            rw [h]
            rw [mySet_MapTwo]
            simp

-- now that we have these two maps, and have proved that they are indeed homomorphisms we want to introduce the notion of an irreducible representation as well as the idea of direct sums.
-- This is where it will start to get interesting!
