import Ctic.Limit.Basic
import Ctic.Limit.Diagram
import Ctic.Repre.Contravariant
import Ctic.Repre.Notation

namespace CTIC

inductive HasLimit {J C : Type*} [Category J] [Category C] (F : J ⥤ C) : Prop where
  | intro (limit : Limit F)

class HasLimitsOfShape (C J : Type*) [Category C] [Category J] : Prop where
  limits : ∀ (F : J ⥤ C), HasLimit F

class HasFiniteProducts (C : Type u) [Category C] : Prop where
  proj : ∀ (n : ℕ), HasLimitsOfShape (Discrete (Fin n)) C
