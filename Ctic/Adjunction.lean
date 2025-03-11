import Ctic.Repre

namespace CTIC

class Adjunction [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟭 C ⟹ (F ⋙ G)
  ε : (G ⋙ F) ⟹ 𝟭 D
  upper {X : C} : F.map (η X) ≫ ε (F X) = 𝟙 (F X) -- top right diagonal diagram
  lower {Y : D} : η (G Y) ≫ G.map (ε Y) = 𝟙 (G Y) -- bottom left diagonal diagram

namespace Adjunction

variable {C : Type u} {D : Type v}
variable [Category C] [Category D]
variable {F : C ⥤ D} {G : D ⥤ C} [Adjunction F G]

example {X : C} {Y : D} : Hom[F X, Y] ≅ Hom[X, G Y] := by
  constructor
  case morphism =>
    simp [HomCov]
    intro f
    let f' := G.map f
    exact η.component X ≫ f'
  case inverse =>
    simp [HomCov]
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
    rw [upper]
    simp
  case backward =>
    simp [Category.comp, Category.id]
    funext f
    simp
    have := (η (F := F) (G := G)).naturality f
    simp [Functor.id, Functor.comp] at this
    rw [this]
    rw [← Category.assoc]
    rw [lower]
    simp

end Adjunction

notation:max "Hom[" F "(" "-" ")" ", " Y "]" => Fᵒᵖ ⋙ Hom[-, Y]
notation:max "Hom[" X ", " F "(" "-" ")" "]" => F ⋙ Hom[X, -]

open Lean in
@[app_unexpander Functor.comp]
def unexpand_Functor_comp_HomCon : PrettyPrinter.Unexpander
  | `($(_) $fᵒᵖ Hom[-, $y]) => `(Hom[$f(-), $y])
  | _ => throw ()

open Lean in
@[app_unexpander Functor.comp]
def unexpand_Functor_comp_HomCov : PrettyPrinter.Unexpander
  | `($(_) $f Hom[$x, -]) => `(Hom[$x, $f(-)])
  | _ => throw ()

open Lean in
@[app_unexpander Functor.obj]
def unexpand_Functor_comp_HomCon_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$f(-), $y] $xᵒᵖ) => `(Hom[$f $x, $y])
  | `($(_) Hom[$f(-), $y] $x) =>
    match x with
    | `({ unop := $x }) => `(Hom[$f $x, $y])
    | _ => `(Hom[$f $xᵒᵖ, $y])
  | _ => throw ()

open Lean in
@[app_unexpander Functor.obj]
def unexpand_Functor_HomCon_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[-, $y] $xᵒᵖ) => `(Hom[$x, $y])
  | `($(_) Hom[-, $y] $x) =>
    match x with
    | `({ unop := $x }) => `(Hom[$x, $y])
    | _ => `(Hom[$xᵒᵖ, $y])
  | _ => throw ()

open Lean in
@[app_unexpander Functor.obj]
def unexpand_Functor_comp_HomCov_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$x, $f(-)] $y) => `(Hom[$x, $f $y])
  | _ => throw ()

open Lean in
@[app_unexpander Functor.obj]
def unexpand_Functor_HomCov_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$x, -] $y) => `(Hom[$x, $y])
  | _ => throw ()

@[simp]
theorem HomCon.comp_obj_def [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] { unop := X } = Hom[F X, Y] := by rfl

@[simp]
theorem HomCon.comp_obj_def' [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] Xᵒᵖ = Hom[F X, Y] := by rfl

@[simp]
theorem Functor.op_map_def [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : C} {f : X ⟶ Y} :
    Fᵒᵖ.map f = F.map f := by rfl

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
    simp [Category.comp, HomCon]
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
    simp [Category.comp, HomCon]
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
    rw [Category.assoc, upper]
    rw [Category.id_comp (f := f)]
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
    simp [Category.comp, Functor.comp, HomCov]
    funext g
    simp
  inverse := by
    use fun Y g => F.map g ≫ ε Y
    intro d Y f
    simp [Category.comp, Functor.comp, HomCov]
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
    rw [Category.id_comp (f := f)]
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
