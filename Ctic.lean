-- This module serves as the root of the `Ctic` library.
-- Import modules here that should be built as part of the library.
import Ctic.Basic
import Mathlib
open CategoryTheory
#check CategoryTheory.instAddHomFunctor
#check CategoryTheory.oppositeShiftFunctorAdd'_hom_app
#check CategoryTheory.NatTrans.id_comm
#check CategoryTheory.NatTrans.id
#synth Category (Opposite Type)
#check Category.opposite
#check IsUniversalColimit
#check Comma
#check Cat
#check Functor.const
