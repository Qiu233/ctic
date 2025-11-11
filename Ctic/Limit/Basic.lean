import Ctic.Category
import Ctic.Functor

namespace CTIC

@[ext]
structure Cone {J C : Type*} [Category J] [Category C] (F : J ⥤ C) where
  N : C
  π' : (Functor.const N) ⟶ F

@[ext]
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
  unique_morphism : ∀ {Y : C} (f : X ⟶ Y), f = morphism Y

class Terminal {C : Type u} [Category C] (Y : C) where
  morphism : (X : C) → X ⟶ Y
  unique_morphism : ∀ {X : C} (f : X ⟶ Y), f = morphism X

theorem Initial.self [Category C] {X : C} {i : Initial X} : i.morphism X = 𝟙 X := by
  have := i.unique_morphism (f := 𝟙 X)
  simp [this]

theorem Terminal.self [Category C] {X : C} {t : Terminal X} : t.morphism X = 𝟙 X := by
  have := t.unique_morphism (f := 𝟙 X)
  simp [this]

structure Limit {J C : Type*} [Category J] [Category C] (F : J ⥤ C) where
  L : Cone F
  final : Terminal L

-- def IsLimitOf [Category J] [Category C] (L : C) (F : J ⥤ C) := ∃ limit : Limit F, limit.L.N = L

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

instance : Category Unit where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  assoc := by simp

@[reducible]
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

@[simp]
theorem TrivialFunctor.map_eq [Category C] {c : C} {f : X ⟶ Y} : (TrivialFunctor c).map f = 𝟙 c := by simp

@[simp]
theorem TrivialFunctor.obj_eq [Category C] {c : C} : (TrivialFunctor c).obj X = c := by simp

@[simp]
theorem TrivialFunctor.obj_eq' [Category C] {c : C} : (TrivialFunctor c) X = c := by simp

private def aux_1 [Category C] [Category D] (F : C ⥤ D) : Cone F ⥤ Comma Δ (TrivialFunctor F) := by
  let obj : Cone F → Comma Δ (TrivialFunctor F) := fun x => Comma.mk x.N () x.π'
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

private def aux_2 [Category C] [Category D] (F : C ⥤ D) : Comma Δ (TrivialFunctor F) ⥤ Cone F := by
  let obj : Comma Δ (TrivialFunctor F) → Cone F := fun x => ⟨x.d, x.f⟩
  let map {X Y : Comma Δ (TrivialFunctor F)} : X ⟶ Y → obj X ⟶ obj Y := fun f => ⟨f.k, by
      intro j
      simp [obj]
      have := f.commu
      simp at this
      rw [this]
      simp [Category.comp]
      congr⟩
  apply Functor.mk (obj := obj) (map := map)

structure CategoryObj.{v, u} where
  C : Type u
  [inst : Category.{v, u} C]

instance (o : CategoryObj) : Category (o.C) := o.inst

structure CategoryObj.Hom.{v, u} (C D : CategoryObj.{v, u}) where
  F : C.C ⥤ D.C
  G : D.C ⥤ C.C
  η' : 𝟭 C.C = (F ⋙ G)
  ε' : (G ⋙ F) = 𝟭 D.C

instance : Category CategoryObj where
  Hom X Y := CategoryObj.Hom X Y
  id X := ⟨𝟭 X.C, 𝟭 X.C, by rfl, by rfl⟩
  comp {X Y Z} f g := by
    use f.F ⋙ g.F, g.G ⋙ f.G
    . conv => rhs; rw [← Functor.assoc]; rhs; rw [Functor.assoc]; lhs; rw [← g.η']
      simp [f.η']
    . conv => lhs; rw [← Functor.assoc]; rhs; rw [Functor.assoc]; lhs; rw [f.ε']
      simp [g.ε']
  assoc {W X Y Z} f g h := by aesop

def Terminal.unique {C : Type*} [Category C] {X Y : C} : Terminal X → Terminal Y → X ≅ Y := by
  intro t1 t2
  refine ⟨t2.morphism X, t1.morphism Y, ?_, ?_⟩
  . have : 𝟙 X = t1.morphism X := t1.unique_morphism _
    rw [this]
    apply t1.unique_morphism
  . have : 𝟙 Y = t2.morphism Y := t2.unique_morphism _
    rw [this]
    apply t2.unique_morphism

def Initial.unique {C : Type*} [Category C] {X Y : C} : Initial X → Initial Y → X ≅ Y := by
  intro t1 t2
  refine ⟨t1.morphism Y, t2.morphism X, ?_, ?_⟩
  . have : 𝟙 X = t1.morphism X := t1.unique_morphism _
    rw [this]
    apply t1.unique_morphism
  . have : 𝟙 Y = t2.morphism Y := t2.unique_morphism _
    rw [this]
    apply t2.unique_morphism

-- def Cone.down [Category C] [Category D] (F : C ⥤ D) : (Cone F) ≅ (Comma Δ (TrivialFunctor F)) where
--   morphism := aux_1 F
--   inverse := aux_2 F
--   forward := by rfl
--   backward := by rfl

-- def Limit.down [Category C] [Category D] (F : C ⥤ D) : (Limit F) ≅ Σ' (c : Comma Δ (TrivialFunctor F)), Terminal c where
--   morphism := by
--     intro ⟨c, t⟩
--     let c' : Comma Δ (TrivialFunctor F) := ⟨c.N, (), c.π'⟩
--     use c'
--     constructor
--     case morphism =>
--       intro ⟨X, n, f⟩
--       let s := t.morphism ⟨X, f⟩
--       exact ⟨s.u, (), by simp [Category.comp, NatTrans.comp]; rw [NatTrans.ext_iff]; funext t; simp [Category.id]; exact (s.universal t).symm⟩
--     case unique =>
--       intro X f
--       simp
