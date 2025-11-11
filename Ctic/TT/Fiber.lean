import Ctic.Functor
import Ctic.Limit

namespace CTIC

-- variable {C : Type u} [Category C] [HasTerminal C]

-- def Fiber {C : Type u} [Category C] [has_terminal : HasTerminal C] {X Y : C} (f : X ⟶ Y) (p : has_terminal.terminal ⟶ Y) : SliceOver Y where

local notation:max C " // " c => @SliceOver C _ c

open Lean PrettyPrinter Delaborator SubExpr Meta in
section

@[delab app.CTIC.SliceOver]
def delab_Isomorphism_morphism_MonoidalCategory : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 3
  let C ← withNaryArg 0 delab
  let c ← withNaryArg 2 delab
  `($C // $c)

end


-- example {C : Type u} [Category C] [has_prod : HasFiniteProducts C] (X : C) : HasFiniteProducts (SliceOver X) where
--   proj n := by
--     apply HasLimitsOfShape.mk
--     intro F
--     have ⟨has_limit⟩ := has_prod.proj n
--     specialize has_limit
