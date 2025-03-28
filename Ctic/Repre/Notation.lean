import Ctic.Repre.Yoneda

namespace CTIC

scoped notation:max "Hom[" x ", " "-" "]" => Functor.obj Yoneda.Covariant.Embedding xᵒᵖ
scoped notation:max "Hom[" x ", " y "]" => Functor.obj Hom[x, -] y
scoped notation:max "Hom[" "-" ", " x "]" => Functor.obj Yoneda.Contravariant.Embedding x

scoped notation:max "Hom[" F "(" "-" ")" ", " Y "]" => Fᵒᵖ ⋙ Hom[-, Y]
scoped notation:max "Hom[" X ", " F "(" "-" ")" "]" => F ⋙ Hom[X, -]

section
open Lean

@[scoped app_unexpander Functor.comp]
private def unexpand_Functor_comp_HomCon : PrettyPrinter.Unexpander
  | `($(_) $fᵒᵖ Hom[-, $y]) => `(Hom[$f(-), $y])
  | _ => throw ()

@[scoped app_unexpander Functor.comp]
private def unexpand_Functor_comp_HomCov : PrettyPrinter.Unexpander
  | `($(_) $f Hom[$x, -]) => `(Hom[$x, $f(-)])
  | _ => throw ()

@[scoped app_unexpander Functor.obj]
private def unexpand_Functor_comp_HomCon_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$f(-), $y] $xᵒᵖ) => `(Hom[$f $x, $y])
  | `($(_) Hom[$f(-), $y] $x) =>
    match x with
    | `({ unop := $x }) => `(Hom[$f $x, $y])
    | _ => `(Hom[$f $xᵒᵖ, $y])
  | _ => throw ()

@[scoped app_unexpander Functor.obj]
private def unexpand_Functor_HomCon_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[-, $y] $xᵒᵖ) => `(Hom[$x, $y])
  | `($(_) Hom[-, $y] $x) =>
    match x with
    | `({ unop := $x }) => `(Hom[$x, $y])
    | _ => `(Hom[$xᵒᵖ, $y])
  | _ => throw ()

@[scoped app_unexpander Functor.obj]
private def unexpand_Functor_comp_HomCov_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$x, $f(-)] $y) => `(Hom[$x, $f $y])
  | _ => throw ()

@[scoped app_unexpander Functor.obj]
private def unexpand_Functor_HomCov_obj : PrettyPrinter.Unexpander
  | `($(_) Hom[$x, -] $y) => `(Hom[$x, $y])
  | _ => throw ()

end

@[simp]
private theorem Yoneda.Contravariant.comp_obj_def [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] { unop := X } = Hom[F X, Y] := by rfl

@[simp]
private theorem Yoneda.Contravariant.comp_obj_def' [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] Xᵒᵖ = Hom[F X, Y] := by rfl

@[simp]
private theorem Yoneda.Contravariant.map_raw [Category C] {c : C} {X Y : C} {f : X ⟶ Y} {g : Y ⟶ c} :
    (Hom[-, c].map f) g = f ≫ g := by rfl

@[simp]
private theorem Yoneda.Contravariant.map [Category C] {c : Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ c} :
    (Hom[-, c].map f) g = f ≫ g := by rfl

@[simp]
private theorem Yoneda.Contravariant.obj [Category C] {c : C} (X : C) :
    Hom[-, c] Xᵒᵖ = Hom[X, c] := by rfl

@[simp]
private theorem Yoneda.Covariant.comp_obj_def [Category C] [Category D] {F : C ⥤ D} {X : D} {Y : C} :
    Hom[X, F(-)] Y = Hom[X, F Y] := by rfl

@[simp]
private theorem Yoneda.Covariant.map [Category C] {c : C} {X Y : C} {f : X ⟶ Y} {g : c ⟶ X} :
    (Hom[c, -].map f) g = g ≫ f := by rfl

-- @[simp]
-- private theorem Yoneda.Covariant.obj [Category C] {c : C} (X : C) :
--     Hom[c, -] X = Hom[c, X] := by rfl

-- @[simp]
-- private theorem reduce_HomCon [Category C] {X : C} : HomCon X = Hom[-, X] := by rfl

-- @[simp]
-- private theorem reduce_HomCov [Category C] {X : C} : HomCov Xᵒᵖ = Hom[X, -] := by rfl

-- @[simp]
-- private theorem reduce_HomCov' [Category C] {X : Cᵒᵖ} : HomCov X = Hom[Xᵒᵖ, -] := by rfl

open Lean PrettyPrinter Delaborator SubExpr Meta in
section

@[delab app.CTIC.HomCon]
private def delab_Functor_con : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 3
  let x ← withNaryArg 2 delab
  `(Hom[-, $x])

@[delab app.CTIC.HomCov]
private def delab_Functor_cov : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 3
  let inop? ← ((e.getArg! 2).app4? ``HasOpposite.op).mapM fun (_, _, _, _) => withNaryArg 2 do withNaryArg 3 do delab
  match inop? with
  | none =>
    let x ← withNaryArg 2 delab
    `(Hom[$xᵒᵖ, -])
  | some inop =>
    `(Hom[$inop, -])

end
