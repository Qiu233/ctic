import Ctic.Category
namespace CTIC

@[ext]
structure Functor (C : Type u) (D : Type v) [Category C] [Category D] where
  obj : C → D
  map {X Y : C} : X ⟶ Y → obj X ⟶ obj Y
  map_id {X : C} : map (𝟙 X) = 𝟙 (obj X) := by aesop
  map_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : map (f ≫ g) = map f ≫ map g := by aesop

attribute [simp] Functor.map_id Functor.map_comp

infixr:300 " ⥤ " => Functor

instance [Category C] [Category D] : CoeFun (C ⥤ D) (fun _ => C → D) := ⟨Functor.obj⟩

open Lean in
@[app_unexpander Functor.obj]
private def unexpand_Functor_obj : PrettyPrinter.Unexpander
  | `($(_) $f $a) => `($f $a)
  | _ => throw ()

def Functor.id (C : Type u) [Category C] : C ⥤ C where
  obj X := X
  map f := f
  map_id := by simp
  map_comp := by simp

def Functor.comp {C D E : Type*} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj := G.obj ∘ F.obj
  map := G.map ∘ F.map
  map_id := by simp [Functor.map_id]
  map_comp := by simp [Functor.map_comp]

infixl:300 " ⋙ " => Functor.comp
prefix:320 "𝟭 " => Functor.id

def Functor.assoc {C D E T : Type*} [Category C] [Category D] [Category E] [Category T] {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ T} : F.comp (G.comp H) = (F.comp G).comp H := by
  simp [Functor.comp]
  apply And.intro
  . funext
    simp
  . funext
    simp

@[simp]
def Functor.id_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : (𝟭 C).comp F = F := by
  obtain ⟨F, Fmap, mi, mc⟩ := F
  simp [Functor.id, Functor.comp]
  apply And.intro
  . funext
    simp
  . funext
    simp

@[simp]
def Functor.comp_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : F.comp (𝟭 D) = F := by
  obtain ⟨F, Fmap, mi, mc⟩ := F
  simp [Functor.id, Functor.comp]
  apply And.intro
  . funext
    simp
  . funext
    simp

def Functor.opposite [Category C] [Category D] (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := Opposite.op (F.obj X.unop)
  map {X Y} f := F.map f
  map_id {X} := by simp [Category.id]
  map_comp {X Y Z f g} := by simp [Category.comp]

@[reducible]
instance [Category C] [Category D] : HasOpposite (C ⥤ D) (Cᵒᵖ ⥤ Dᵒᵖ) where
  op F := F.opposite

@[simp]
private theorem reduce_functor_op.«1» [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (Fᵒᵖ Xᵒᵖ)ᵒᵖ = F X := rfl

@[simp]
private theorem reduce_functor_op.«2» [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (Fᵒᵖ (Opposite.op X))ᵒᵖ = F X := rfl

@[simp]
private theorem reduce_functor_op.«3» [Category C] [Category D] (F : C ⥤ D) (X : Cᵒᵖ) :
    (Fᵒᵖ X)ᵒᵖ = F Xᵒᵖ := rfl

@[simp]
private theorem reduce_functor_op.«3'» [Category C] [Category D] (F : C ⥤ D) (X : Opposite C) :
    (Fᵒᵖ X)ᵒᵖ = F Xᵒᵖ := rfl

instance Category.product (C : Type u) (D : Type v) [Category C] [Category D] : Category (C × D) where
  Hom X Y := PProd (X.fst ⟶ Y.fst) (X.snd ⟶ Y.snd)
  id X := ⟨𝟙 X.fst, 𝟙 X.snd⟩
  comp {X Y Z} := fun ⟨fc, fd⟩ ⟨gc, gd⟩ => ⟨fc ≫ gc, fd ≫ gd⟩
  assoc {W X Y Z} := by simp [Category.assoc]

theorem Functor.iso {C : Type u} {D : Type v} [Category C] [Category D] {F : C ⥤ D} {X Y : C} {f : X ⟶ Y} : Invertible f → Invertible (F.map f) := by
  intro ⟨i, iso⟩
  use F.map i
  simp [← Functor.map_comp, iso, Functor.map_id]

@[simp]
private lemma Functor.id_obj [Category C] : (𝟭 C).obj X = X := by simp [Functor.id]

@[simp]
private lemma Functor.id_obj' [Category C] : (𝟭 C) X = X := by simp [Functor.id]
