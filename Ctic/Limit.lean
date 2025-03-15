import Ctic.Category
import Ctic.Functor

namespace CTIC

-- variable {C : Type u} {D : Type v} [Category C] [Category D]


structure Cone {J C : Type*} [Category J] [Category C] (F : J ⥤ C) where
  N : C
  π' : (constFunctor N) ⟶ F

structure ConeHom {J C : Type*} [Category J] [Category C] {F : J ⥤ C} (X Y : Cone F) where
  u : X.N ⟶ Y.N
  universal : ∀ j : J, u ≫ (Y.π'.component j) = (X.π'.component j)

instance {J : Type u} {C : Type v} [Category J] [Category C] (F : J ⥤ C) : Category (Cone F) where
  Hom X Y := ConeHom X Y
  id X := ⟨𝟙 X.N, by simp⟩
  comp f g := ⟨f.u ≫ g.u,
    by intro j; simp [← Category.assoc, g.universal, f.universal]⟩
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

class Initial {C : Type u} [Category C] (X : C) where
  morphism : (Y : C) → X ⟶ Y
  unique : ∀ {Y : C} {f : X ⟶ Y}, f = morphism Y

class Terminal {C : Type u} [Category C] (Y : C) where
  morphism : (X : C) → X ⟶ Y
  unique : ∀ {X : C} {f : X ⟶ Y}, f = morphism X

theorem Initial.self [Category C] {X : C} {i : Initial X} : i.morphism X = 𝟙 X := by
  have := i.unique (f := 𝟙 X)
  simp [this]

theorem Terminal.self [Category C] {X : C} {t : Terminal X} : t.morphism X = 𝟙 X := by
  have := t.unique (f := 𝟙 X)
  simp [this]

class Limit {J : Type u1} {C : Type u2} [Category J] [Category C] (F : J ⥤ C) where
  L : Cone F
  final : Terminal L

def IsLimitOf [Category J] [Category C] (L : C) (F : J ⥤ C) := ∃ limit : Limit F, limit.L.N = L

-- C(c, -)
@[reducible]
def HomCov [Category.{v, u} C] (c : Cᵒᵖ) : C ⥤ Type v where
  obj X := cᵒᵖ ⟶ X
  map {X Y} f i := i ≫ f
  map_id := by
    simp [Category.id, ← funext_iff]
    unfold id
    simp
  map_comp {X Y Z} f g := by
    simp [Category.comp]
    funext f'
    simp

-- C(-, c)
@[reducible]
def HomCon [Category.{v, u} C] (c : C) : Cᵒᵖ ⥤ Type v where
  obj X := X.unop ⟶ c
  map {X Y} f i := f ≫ i
  map_id := by
    simp [Category.id, ← funext_iff]
    unfold id
    simp
  map_comp {X Y Z} f g := by
    simp [Category.comp]
    funext f'
    simp

-- abbrev BiFunctor (C D E : Type*) [Category C] [Category D] [Category E] := C ⥤ D ⥤ E

-- structure CommaLeft [Category.{u1, v1} C] [Category.{u2, v2} D] (F : D ⥤ C) (c : C) : Type max u1 u2 v1 v2 where
--   d : D
--   f : F.obj d ⟶ c

instance : Category Unit where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  assoc := by simp

def TrivialFunctor [Category C] (c : C) : Unit ⥤ C where
  obj _ := c
  map _ := 𝟙 c

@[simp]
private theorem TrivialFunctor.app [Category C] (c : C) (u : Unit) : (TrivialFunctor c) u = c := by rfl

@[simp]
private theorem TrivialFunctor.map [Category C] (c : C) {X Y : Unit} (f : X ⟶ Y) : (TrivialFunctor c).map f = 𝟙 c := by rfl

open Lean PrettyPrinter Delaborator SubExpr Meta in
section

@[delab app.CTIC.Functor.obj]
def delab_TrivialFunctor_obj : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOf ``TrivialFunctor
    guard <| e.getAppNumArgs == 3
    withNaryArg 2 delab

end

-- def TrivialFunctor.target [Category C] (f : ) :=

-- abbrev T [Category J] [Category C] (F : J ⥤ C) := Comma Functor.const (TrivialFunctor F)

-- example [Category J] [Category C] (F : J ⥤ C) {X : Comma Functor.const (TrivialFunctor F)} : Nonempty (Terminal X) ↔ IsLimitOf X.d F := by
--   apply Iff.intro
--   . intro ⟨⟨mor, unique⟩⟩
--     let t : Cone F := ⟨X.d, X.f⟩
--     have : Terminal t := by
--       apply Terminal.mk
--       case morphism =>
--         intro Y
--         let obj1 : Comma Functor.const (TrivialFunctor F) → Cone F := fun x => ⟨x.d, x.f⟩
--         let obj2 : Cone F → Comma Functor.const (TrivialFunctor F) := fun x => Comma.mk x.N () x.π'
--         let t2 := mor (obj2 Y)
--         simp [obj2] at t2
--         simp [t]
--         -- let Y' := Comma.mk Y.N (F.obj ()) Y.π'
--         -- simp [Category.Hom]
--         -- apply ConeHom.mk
--     simp [IsLimitOf]

@[simp]
theorem TrivialFunctor.map_eq [Category C] {c : C} {f : X ⟶ Y} : (TrivialFunctor c).map f = 𝟙 c := by simp [TrivialFunctor]

@[simp]
theorem TrivialFunctor.obj_eq [Category C] {c : C} : (TrivialFunctor c).obj X = c := by simp [TrivialFunctor]

@[simp]
theorem TrivialFunctor.obj_eq' [Category C] {c : C} : (TrivialFunctor c) X = c := by simp [TrivialFunctor]

private def aux_1 [Category C] [Category D] (F : C ⥤ D) : Comma Functor.const (TrivialFunctor F) ⥤ Cone F := by
    let obj : Comma Functor.const (TrivialFunctor F) → Cone F := fun x => ⟨x.d, x.f⟩
    let map {X Y : Comma Functor.const (TrivialFunctor F)} : X ⟶ Y → obj X ⟶ obj Y := fun f => ⟨f.k, by
        intro j
        simp
        have := f.commu
        simp at this
        rw [this]
        simp [Category.comp]
        congr⟩
    apply Functor.mk (obj := obj) (map := map)

private def aux_2 [Category C] [Category D] (F : C ⥤ D) : Cone F ⥤ Comma Functor.const (TrivialFunctor F) := by
    let obj : Cone F → Comma Functor.const (TrivialFunctor F) := fun x => Comma.mk x.N () x.π'
    let map {X Y : Cone F} : X ⟶ Y → obj X ⟶ obj Y := fun f => ⟨f.u, 𝟙 (), by
      simp [obj]
      rw [NatTrans.ext_iff]
      funext t
      simp [Functor.const, Category.comp, NatTrans.comp]
      exact (f.universal t).symm⟩
    apply Functor.mk (obj := obj) (map := map) ?_ ?_
    . intro X
      simp [map, obj, Category.id]
    . intro X Y Z f g
      simp [map, Category.comp]
      congr

example [Category C] [Category D] (F : C ⥤ D) : Category.Equivalence (Comma Functor.const (TrivialFunctor F)) (Cone F) where
  F := aux_1 F
  G := aux_2 F
  η' := by
    simp [aux_1, aux_2, Functor.id, Functor.comp]
    apply Isomorphism.mk
    case morphism =>
      apply NatTrans.mk (fun X => 𝟙 X)
      intro X Y f
      simp
      rfl
    case inverse =>
      apply NatTrans.mk (fun X => 𝟙 X)
      intro X Y f
      simp
      rfl
    case forward => simp [Functor.comp, Category.comp, Functor.id, Category.id, NatTrans.comp]; simp [NatTrans.id]; rfl
    case backward => simp [Functor.comp, Category.comp, Functor.id, Category.id, NatTrans.comp]; simp [NatTrans.id]; rfl
  ε' := by
    simp [aux_1, aux_2, Functor.id, Functor.comp]
    apply Isomorphism.mk
    case inverse =>
      simp [Category.Hom]
      apply NatTrans.mk (fun X => 𝟙 X)
      intro X Y f
      simp
      rfl
    case morphism =>
      simp [Category.Hom]
      apply NatTrans.mk (fun X => 𝟙 X)
      intro X Y f
      simp
      rfl
    case forward => simp [Functor.comp, Category.comp, Functor.id, Category.id, NatTrans.comp]; simp [NatTrans.id]; rfl
    case backward => simp [Functor.comp, Category.comp, Functor.id, Category.id, NatTrans.comp]; simp [NatTrans.id]; rfl

def Discrete (α : Type u) := α

instance [DecidableEq α] : DecidableEq (Discrete α) := inferInstance

instance : Category (Discrete α) where
  Hom X Y := PLift (X = Y)
  id X := ⟨by simp⟩
  comp f g := ⟨Eq.trans f.down g.down⟩
  assoc := by simp

inductive Discrete.Binary : Type u where
  | X | Y
deriving BEq

notation:max "𝟐" => Discrete Discrete.Binary

@[simp]
private abbrev BinProd.obj [Category C] (X Y : C) : 𝟐 → C := fun x =>
  match x with
  | .X => X
  | .Y => Y

@[simp]
private abbrev BinProd.map [Category C] (X Y : C) {A B : 𝟐} : (A ⟶ B) → (BinProd.obj X Y A ⟶ BinProd.obj X Y B) := fun f => by
  simp [BinProd.obj]
  rw [f.down]
  cases B with
  | X => exact 𝟙 X
  | Y => exact 𝟙 Y

@[reducible]
def BinProd.functor [inst : Category C] (X Y : C) : 𝟐 ⥤ C where
  obj := BinProd.obj X Y
  map := BinProd.map X Y
  map_id {A} := by cases A <;> simp
  map_comp {A B C} f g := by
    cases A <;> (cases B <;> (cases C <;> simp [f.down, g.down]))
    . simp [Category.Hom] at f
      apply False.elim f.down
    . simp [Category.Hom] at f
      apply False.elim f.down

@[reducible]
def BinProd [Category C] (X Y : C) := Limit (BinProd.functor X Y)

-- instance [Category C] {A B : C} : Category (BinProd A B) where
--   Hom X Y := X.L ⟶ Y.L
--   id X := 𝟙 X.L
--   comp f g := f ≫ g
--   assoc := by simp

-- structure CatOfBinProd (C : Type u) [Category C] where
--   A : C
--   B : C
--   prod : BinProd A B

-- instance [Category C] : Category (CatOfBinProd C) where
--   Hom X Y := (p : X.prod.L.N ⟶ Y.prod.L.N) ×' ()
-- #check Comma ()
-- #check HomCov

def Hom {C : Type u} [Category.{v} C] : (Cᵒᵖ × C) ⥤ Type v where
  obj := fun (X, Y) => X.unop ⟶ Y
  map {X Y} := fun ⟨f, h⟩ g => f ≫ g ≫ h
  map_id {X} := by
    funext g
    simp [Category.id]
  map_comp {X Y Z f g} := by
    funext h
    simp [Category.comp, Category.assoc]
