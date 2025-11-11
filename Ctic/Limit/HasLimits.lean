import Ctic.Limit.Basic
import Ctic.Limit.Diagram
import Ctic.Repre.Contravariant
import Ctic.Repre.Notation

namespace CTIC

abbrev HasLimit {J C : Type*} [Category J] [Category C] (F : J ⥤ C) : Prop := Nonempty (Limit F)

class HasLimitsOfShape (C J : Type*) [Category C] [Category J] : Prop where
  limits : ∀ (F : J ⥤ C), HasLimit F

class HasFiniteProducts (C : Type u) [Category C] : Prop where
  proj : ∀ (n : ℕ), HasLimitsOfShape (Discrete (Fin n)) C

open Diagram in
abbrev HasTerminal (C : Type*) [Category C] : Prop := HasLimitsOfShape C 𝟬

example : HasTerminal Type where
  limits F := by
    apply Nonempty.intro
    let c : Cone F := ⟨Unit, ⟨(fun x y => by exfalso; apply Diagram.Nullary.empty x), by simp⟩⟩
    use c
    apply Terminal.mk
    case morphism =>
      intro ⟨L, π⟩
      simp [c]
      simp [Category.Hom]
      use fun _ => ()
      intro j
      exfalso
      apply Diagram.Nullary.empty j
    case unique_morphism =>
      intro L f
      simp
      congr
