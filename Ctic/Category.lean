import Aesop
import Mathlib.Logic.Equiv.Basic
namespace CTIC

-- attribute [ext] ULift PLift

class Category.{v, u} (C : Type u) : Type max u (v + 1) where
  Hom : C → C → Sort (v + 1)
  id : ∀ (x : C), Hom x x
  comp : ∀ {x y z : C}, Hom x y → Hom y z → Hom x z
  id_comp : ∀ {x y : C} {f : Hom x y}, comp (id x) f = f := by aesop
  comp_id : ∀ {x y : C} {f : Hom x y}, comp f (id y) = f := by aesop
  assoc : ∀ {w x y z : C} {f : Hom w x} {g : Hom x y} {h : Hom y z}, comp f (comp g h) = comp (comp f g) h

abbrev SmallCategory.{u} := Category.{u, u}

instance [inst : SmallCategory.{u} C] : Category.{u, u} C := inst

infix:300 " ⟶ " => Category.Hom
prefix:320 "𝟙 " => Category.id
infixl:300 " ≫ " => Category.comp

attribute [simp] Category.id_comp Category.comp_id Category.assoc

instance : Category.{u} (Type u) where
  Hom x y := x → y
  id x := _root_.id
  comp f g := Function.comp g f
  id_comp {x y f} := by simp [Function.comp_def]
  comp_id {x y f} := by simp [Function.comp_def]
  assoc {w x y z f g h} := by simp [Function.comp_def]

variable {C : Type u} [Category.{v} C] {X Y : C} in
section

structure Isomorphism (X Y : C) where
  morphism : X ⟶ Y
  inverse : Y ⟶ X
  forward : morphism ≫ inverse = 𝟙 X
  backward : inverse ≫ morphism = 𝟙 Y
infix:100 " ≅ " => Isomorphism

attribute [simp] Isomorphism.forward Isomorphism.backward

instance : CoeOut (X ≅ Y) (X ⟶ Y) where
  coe f := f.morphism

private theorem Isomorphism.ext_aux {f g : X ≅ Y} : f.morphism = g.morphism → f.inverse = g.inverse := by
  intro h
  rw [← Category.id_comp (f := f.inverse)]
  rw [← Category.comp_id (f := g.inverse)]
  rw [← f.forward]
  rw [Category.assoc]
  rw [h]
  rw [g.backward]

@[ext]
theorem Isomorphism.ext {f g : X ≅ Y} : f.morphism = g.morphism → f = g := fun h => by
  have h2 := Isomorphism.ext_aux h
  cases f; congr

def Isomorphism.id [Category C] (X : C) : X ≅ X := Isomorphism.mk (𝟙 X) (𝟙 X) (by simp) (by simp)

def Invertible (f : X ⟶ Y) : Prop := ∃ (g : Y ⟶ X), f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

@[simp]
theorem Isomorphism.invertible (f : X ≅ Y) : Invertible f.morphism := by
  exists f.inverse
  simp [f.forward, f.backward]

noncomputable def Isomorphism.of_invertible {f : X ⟶ Y} (inv : Invertible f) : X ≅ Y where
  morphism := f
  inverse := inv.choose
  forward := by simp [inv.choose_spec]
  backward := by simp [inv.choose_spec]

@[symm]
def Isomorphism.symm (f : X ≅ Y) : Y ≅ X where
  morphism := f.inverse
  inverse := f.morphism
  forward := f.backward
  backward := f.forward

@[trans]
def Isomorphism.comp (f : X ≅ Y) (g : Y ≅ Z) : X ≅ Z where
  morphism := f.morphism ≫ g.morphism
  inverse := g.inverse ≫ f.inverse
  forward := by
    simp [Category.assoc]
    conv =>
      lhs
      lhs
      rw [← Category.assoc]
      rhs
      simp
    simp
  backward := by
    simp [Category.assoc]
    conv =>
      lhs
      lhs
      rw [← Category.assoc]
      rhs
      simp
    simp

@[simp]
theorem Isomorphism.invertible_inv (f : X ≅ Y) : Invertible f.inverse := by
  have := f.symm.invertible
  simp [Isomorphism.symm] at this
  apply this

class Groupoid (C : Type u) extends Category C where
  iso {X Y : C} (f : X ⟶ Y) : Invertible f

@[ext]
structure SliceUnder (c : C) : Type max u v where
  var : C
  hom : c ⟶ var

abbrev SliceUnderHom {c : C} (f g : SliceUnder c) :=
  { h : f.var ⟶ g.var // f.hom ≫ h = g.hom }

@[ext]
structure SliceOver (c : C) : Type max u v where
  var : C
  hom : var ⟶ c

abbrev SliceOverHom {c : C} (f g : SliceOver c) :=
  { h : f.var ⟶ g.var // h ≫ g.hom = f.hom }

--     c
--  f/   \g
--  x -h- y
instance sliceUnder [Category C] (c : C) : Category (SliceUnder c) where
  Hom f g := SliceUnderHom f g
  id x := ⟨𝟙 x.var, by simp⟩
  comp {x y z} f g := ⟨f.val ≫ g.val, by simp [Category.assoc, f.property, g.property]⟩
  assoc {w x y z} f g h := by simp [Category.assoc]

--  x -h- y
--  f\   /g
--     c
instance sliceOver [Category C] (c : C) : Category (SliceOver c) where
  Hom f g := SliceOverHom f g
  id x := ⟨𝟙 x.var, by simp⟩
  comp {x y z} f g := ⟨f.val ≫ g.val, by simp [← Category.assoc, f.property, g.property]⟩
  assoc {w x y z} f g h := by simp [Category.assoc]

structure Opposite (C : Type u) where
  op ::
  unop : C

class HasOpposite (α : Sort u) (β : outParam (Sort v)) where
  op : α → β

attribute [reducible] HasOpposite.op

postfix:max "ᵒᵖ" => HasOpposite.op

@[reducible]
instance op_type.«0» : HasOpposite (Type u) (Type u) where
  op α := Opposite α

@[reducible]
instance op_cat.«0» [Category C] : HasOpposite C Cᵒᵖ where
  op := Opposite.op

@[reducible]
instance op_cat.«1» [Category C] : HasOpposite Cᵒᵖ C where
  op := Opposite.unop

@[reducible]
instance op_cat.«2» [Category C] : HasOpposite C (Opposite C) := op_cat.«0»

@[reducible]
instance op_cat.«3» [Category C] : HasOpposite (Opposite C) C := op_cat.«1»

@[simp]
theorem reduce_op_op.«1» (X : C) : Xᵒᵖᵒᵖ = X := by rfl

@[simp]
private theorem reduce_op_op.«2» (X : C) : Xᵒᵖ.unop = X := by rfl

@[simp]
private theorem reduce_op_op.«3» (X : Cᵒᵖ) : X.unopᵒᵖ = X := by rfl

@[simp]
private theorem reduce_op_op.«3'» (X : Opposite C) : X.unopᵒᵖ = X := by rfl

@[simp]
private theorem reduce_op_op.«4» (X : Cᵒᵖ) : Xᵒᵖᵒᵖ = X := by rfl

@[simp]
private theorem reduce_op_op.«4'» (X : Opposite C) : Xᵒᵖᵒᵖ = X := by rfl

@[simp]
private theorem reduce_op_op.«5» (X : Cᵒᵖ) : X.unop = Xᵒᵖ := by rfl

private theorem reduce_op_op.«5'» (X : Opposite C) : X.unop = Xᵒᵖ := by rfl

@[simp]
private theorem reduce_op_op.«6» (X : C) :
    @HasOpposite.op _ _ op_cat.«1» { unop := X : Cᵒᵖ } = X := by rfl

@[simp]
private theorem reduce_op_op.«7» (X : C) :
    @HasOpposite.op _ _ op_cat.«1» { unop := X : Cᵒᵖ } = X := by rfl

@[simp]
private theorem reduce_op_op_id_comp.«1» (X Y : C) (f : X ⟶ Y) : Category.comp (x := Xᵒᵖᵒᵖ) (y := X) (z := Y) (𝟙 X) f = f := by
  rw [Category.id_comp (x := X)]

@[simp]
private theorem reduce_op_op_id_comp.«2» (X Y : C) (f : X ⟶ Y) : Category.comp (x := X) (y := Xᵒᵖᵒᵖ) (z := Y) (𝟙 X) f = f := by
  rw [Category.id_comp (x := X)]

@[simp]
private theorem reduce_op_op_comp_id.«1» (X Y : C) (f : X ⟶ Y) : Category.comp (x := X) (y := Y) (z := Yᵒᵖᵒᵖ) f (𝟙 Y) = f := by
  rw [Category.comp_id (y := Y)]

@[simp]
private theorem reduce_op_op_comp_id.«2» (X Y : C) (f : X ⟶ Y) : Category.comp (x := X) (y := Yᵒᵖᵒᵖ) (z := Y) f (𝟙 Y) = f := by
  rw [Category.comp_id (y := Y)]

@[reducible, simp]
instance Category.opposite [inst : Category C] : Category Cᵒᵖ where
  Hom x y := inst.Hom y.unop x.unop
  id x := inst.id x.unop
  comp {x y z} f g := inst.comp g f
  assoc {w x y z} f g h := by simp

open Lean in
@[app_unexpander Opposite.unop]
private def unexpand_Opposite_unop : PrettyPrinter.Unexpander
  | `($(_) $x) => `($xᵒᵖ)
  | _ => throw ()

instance [Category C] : Category (Opposite C) := Category.opposite

example {c : C} (f : X ≅ Y) : (c ⟶ X) ≃ (c ⟶ Y) := by
  let toFun : (c ⟶ X) → (c ⟶ Y) := fun α => α ≫ f.morphism
  let invFun : (c ⟶ Y) → (c ⟶ X) := fun α => α ≫ f.inverse
  refine Equiv.mk toFun invFun ?_ ?_
  . intro p
    simp [toFun, invFun, ← Category.assoc]
  . intro p
    simp [toFun, invFun, ← Category.assoc]

def Monic (f : X ⟶ Y) := ∀ ⦃W : C⦄ (g h : W ⟶ X), g ≫ f = h ≫ f → g = h

def Epic (f : X ⟶ Y) := ∀ ⦃Z : C⦄ (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

theorem Epic.of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Epic f → Epic g → Epic (f ≫ g) := by
  simp [Epic]
  intro h1 h2 W h i h3
  apply h2
  apply h1
  simp [h3]

theorem Invertible.monic_and_epic {f : X ⟶ Y} : Invertible f → Monic f ∧ Epic f := by
  intro ⟨g', h1, h2⟩
  apply And.intro
  . intro W g h h3
    rw [← Category.comp_id (f := g)]
    rw [← h1]
    rw [Category.assoc]
    rw [h3]
    rw [← Category.assoc]
    simp [h1]
  . intro W g h h3
    rw [← Category.id_comp (f := h)]
    rw [← h2]
    rw [← Category.assoc]
    rw [← h3]
    rw [Category.assoc]
    simp [h2]

theorem Isomorphism.monic_and_epic (f : X ≅ Y) : Monic f.morphism ∧ Epic f.morphism := f.invertible.monic_and_epic

theorem Isomorphism.monic (f : X ≅ Y) : Monic f.morphism := f.invertible.monic_and_epic.left
theorem Isomorphism.epic (f : X ≅ Y) : Epic f.morphism := f.invertible.monic_and_epic.right

theorem Isomorphism.monic_inverse (f : X ≅ Y) : Monic f.inverse := f.symm.monic
theorem Isomorphism.epic_inverse (f : X ≅ Y) : Epic f.inverse := f.symm.epic

@[ext]
structure Monomorphism (X Y : C) where
  toFun : X ⟶ Y
  monic : Monic toFun

@[ext]
structure Epimorphism (X Y : C) where
  toFun : X ⟶ Y
  epic : Epic toFun

instance : Coe (Monomorphism X Y) (X ⟶ Y) := ⟨Monomorphism.toFun⟩
instance : Coe (Epimorphism X Y) (X ⟶ Y) := ⟨Epimorphism.toFun⟩

infix:300 " ↣ " => Monomorphism
infix:300 " ↠ " => Epimorphism

def Monomorphism.comp (f : X ↣ Y) (g : Y ↣ Z) : X ↣ Z where
  toFun := f.toFun ≫ g.toFun
  monic {W} f1 f2 h := by
    apply f.monic
    apply g.monic
    simp [← Category.assoc, h]

/--
The converse does not hold generally, but holds for sets/types.
See the example below.
-/
theorem Monic.of_comp {f : X ⟶ Y} {g : Y ⟶ Z} : Monic (f ≫ g) → Monic f := by
  intro h1 W α β h2
  apply h1
  simp [Category.assoc, h2]

theorem Monomorphism.monic_of_comp {f : X ↣ Y} {g : X ⟶ W} {h : W ⟶ Y} : f.toFun = g ≫ h → Monic g := by
  intro h1
  apply Monic.of_comp (g := h)
  simp [← h1, f.monic]

/--
Monomorphisms are precisely injections for sets/types.
-/
theorem Function.Monic_iff_Injective {X Y : Type u} {f : X ⟶ Y} : Monic f ↔ Function.Injective f := by
  constructor
  . intro h1 x y h2
    simp [Monic] at h1
    simp [Category.Hom, Category.comp] at h1
    let g : ULift (Fin 2) → X := fun t => if t = ⟨0⟩ then x else y
    let h : ULift (Fin 2) → X := fun t => if t = ⟨0⟩ then y else x
    have : f ∘ g = f ∘ h := by
      funext t
      simp [g, h]
      split
      . exact h2
      . exact h2.symm
    have := h1 g h this
    have conf := funext_iff.mp this ⟨0⟩
    simp [g, h] at conf
    exact conf
  . intro h1 W g h h2
    funext x
    apply h1 (funext_iff.mp h2 x)

theorem Function.Epic_iff_Surjective {X Y : Type u} [DecidableEq Y] {f : X ⟶ Y} : Epic f ↔ Function.Surjective f := by
  constructor
  . intro e b
    simp [Epic] at e
    apply not_not.mp
    intro h1
    simp at h1
    let g : Y → ULift.{u, 0} (Fin 2) := fun t => if t = b then ⟨1⟩ else ⟨0⟩
    let h : Y → ULift.{u, 0} (Fin 2) := fun t => ⟨0⟩
    have h2 := e g h
    have h3 : f ≫ g = f ≫ h := by
      funext t
      simp [Category.comp]
      trans ⟨0⟩
      . simp [g]
        simp [h1]
      . simp [h]
    have h4 := h2 h3
    have h5 : g b ≠ h b := by simp [g, h]
    apply h5
    simp [h4]
  . intro surj Z g h h1
    simp [Function.Surjective] at surj
    simp [Category.comp] at h1
    funext t
    have ⟨a, ha⟩ := surj t
    cases ha
    revert a
    rw [← funext_iff]
    rw [← Function.comp_def]
    rw [← Function.comp_def]
    exact h1

/-- X ↣ Y ↠ X -/
structure Retract [Category C] (Y : C) where
  X : C
  sec : X ↣ Y
  ret : Y ↠ X
  inv : sec.toFun ≫ ret.toFun = 𝟙 X

/-- exercise 1.2.vi -/
def Isomorphism.of_monic_retract [Category C] {Y : C} {R : Retract Y} : Monic R.ret.toFun → R.X ≅ Y := by
  obtain ⟨X, s, r, hinv⟩ := R
  simp
  intro hm
  apply Isomorphism.mk s r hinv
  apply hm
  simp [← Category.assoc, hinv]

/-- exercise 1.2.vi -/
def Isomorphism.of_epic_section [Category C] {Y : C} {R : Retract Y} : Epic R.sec.toFun → R.X ≅ Y := by
  obtain ⟨X, s, r, hinv⟩ := R
  simp
  intro hm
  apply Isomorphism.mk s r hinv
  apply hm
  simp [Category.assoc, hinv]
