import Ctic.Functor.Comma
namespace CTIC

def Functor.const {C D : Type*} [Category C] [Category D] : D ⥤ C ⥤ D where
  obj d := { obj := fun _ => d, map := fun _ => 𝟙 d }
  map {X Y} f := NatTrans.mk (fun _ => f) (by simp)

scoped notation:max "Δ" => Functor.const

-- def constFunctor {C D : Type*} [Category C] [Category D] (d : D) : C ⥤ D := Functor.const.obj d

-- @[simp]
-- private lemma constFunctor.eta [Category C] [Category D] {X : D} {Y : C} : (constFunctor X).obj Y = X := by simp [constFunctor, Functor.const]

-- @[simp]
-- private lemma constFunctor.map [Category C] [Category D] {d : D} {X Y : C} {f : X ⟶ Y} : (constFunctor d).map f = 𝟙 d := by simp [constFunctor, Functor.const]

@[simp]
private lemma Functor.const.eta [Category C] [Category D] {X : D} {Y : C} : (Functor.const.obj X).obj Y = X := by simp [Functor.const]

@[simp]
private lemma Functor.const.map [Category C] [Category D] {d : D} {X Y : C} {f : X ⟶ Y} : (Functor.const.obj d).map f = 𝟙 d := by simp [Functor.const]

open Lean in
@[app_unexpander Functor.obj]
private def unexpand_Functor_obj : PrettyPrinter.Unexpander
  | `($(_) $f $a) => `($f $a)
  | _ => throw ()

@[simp]
private lemma Functor.const.map2 [Category C] [Category D] {d : D} {X Y : C} {f : X ⟶ Y} : (Functor.const d).map f = 𝟙 d := by simp [Functor.const]

-- @[simp]
-- private lemma constFunctor.eta2 [Category C] [Category D] {X : D} {Y : C} : constFunctor X Y = X := by simp [constFunctor, Functor.const]

@[simp]
private lemma Functor.const.eta2 [Category C] [Category D] {X : D} {Y : C} : (Functor.const X).obj Y = X := by simp [Functor.const]

@[simp]
private lemma Functor.const.eta3 [Category C] [Category D] {X : D} {Y : C} : Functor.const X Y = X := by simp [Functor.const]

@[simp]
private lemma Functor.const.eta4 [Category C] [Category D] {X : D} {Y : C} : (Functor.const X).obj Y = X := by simp [Functor.const]

abbrev over.{v, u} [Category.{v, u} C] (c : C) := Comma (𝟭 C) (Functor.const (C := C) c)

abbrev under.{v, u} [Category.{v, u} C] (c : C) := Comma (Functor.const (C := C) c) (𝟭 C)

instance [Category C] (c : C) : Category (over c) := inferInstance
instance [Category C] (c : C) : Category (under c) := inferInstance
