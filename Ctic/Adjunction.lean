import Ctic.Repre

namespace CTIC

class Adjunction [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟭 C ⟹ (F ⋙ G)
  ε : (G ⋙ F) ⟹ 𝟭 D
  upper {X : C} : F.map (η X) ≫ ε (F X) = 𝟙 (F X) -- top right diagonal diagram
  lower {Y : D} : η (G Y) ≫ G.map (ε Y) = 𝟙 (G Y) -- bottom left diagonal diagram

infix:350 " ⊣ " => Adjunction

namespace Adjunction

variable {C : Type u} {D : Type v}
variable [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C} [Adjunction F G]

example {X : C} {Y : D} : Hom[F X, Y] ≅ Hom[X, G Y] := by
  constructor
  case morphism =>
    intro f
    let f' := G.map f
    exact η.component X ≫ f'
  case inverse =>
    intro g
    let g' := F.map g
    exact g' ≫ ε.component Y
  case forward =>
    simp [Category.comp, Category.id]
    funext f
    simp
    have := (ε (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [← Category.assoc]
    rw [← this]
    rw [Category.assoc]
    change F.map (η X) ≫ ε (F X) ≫ f = f
    rw [upper]
    rw [Category.id_comp (x := F X)]
  case backward =>
    simp [Category.comp, Category.id]
    funext f
    simp
    have := (η (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    change η X ≫ G.map (F.map f) = f ≫ η (G Y) at this
    rw [this]
    rw [← Category.assoc]
    rw [lower]
    simp

end Adjunction

namespace Adjunction

variable {C : Type u} {D : Type v}
variable [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C} [Adjunction F G]

def Sharp (Y : D) : Hom[F(-), Y] ≅ Hom[-, G Y] where
  morphism := by
    use fun ⟨X⟩ f => η X ≫ G.map f
    intro ⟨X⟩ ⟨c⟩
    simp [Category.Hom]
    intro f
    funext h
    simp [Category.comp]
    simp [Functor.comp]
    congr 1
    have := (η (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [this]
  inverse := by
    use fun ⟨X⟩ g => F.map g ≫ ε Y
    intro ⟨X⟩ ⟨c⟩
    simp [Category.Hom]
    intro f
    funext h
    simp [Category.comp]
    simp [Functor.comp]
  forward := by
    simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext X
    obtain ⟨X⟩ := X
    simp
    funext f
    simp
    have := (ε (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [← Category.assoc, ← this]
    rw [Category.assoc]
    simp [HasOpposite.op, Functor.opposite]
    rw [upper]
    rw [Category.id_comp (x := F X)]
  backward := by
    simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext X
    obtain ⟨X⟩ := X
    simp
    funext f
    simp
    have := (η (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [this]
    rw [← Category.assoc, lower]
    rw [Category.comp_id]

def Flat (X : C) : Hom[F X, -] ≅ Hom[X, G(-)] where
  morphism := by
    use fun Y f => η X ≫ G.map f
    intro d Y f
    simp [Category.comp, Functor.comp]
    funext g
    simp
  inverse := by
    use fun Y g => F.map g ≫ ε Y
    intro d Y f
    simp [Category.comp, Functor.comp]
    funext g
    simp
    rw [← Category.assoc]
    rw [← Category.assoc]
    congr 1
    have := (ε (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [this]
  forward := by
    simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext Y f
    simp
    have := (ε (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [← Category.assoc, ← this]
    rw [Category.assoc, upper]
    simp
  backward := by
    simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext Y f
    simp
    have := (η (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [this]
    rw [← Category.assoc, lower]
    rw [Category.comp_id]


end Adjunction
