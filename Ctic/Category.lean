import Aesop
import Mathlib.Logic.Equiv.Basic
namespace CTIC

class Category (V : Type u) where
  Hom : V → V → Sort v
  id : ∀ (x : V), Hom x x
  comp : ∀ {x y z : V}, Hom x y → Hom y z → Hom x z
  id_comp : ∀ {x y : V} {f : Hom x y}, comp (id x) f = f := by aesop
  comp_id : ∀ {x y : V} {f : Hom x y}, comp f (id y) = f := by aesop
  assoc : ∀ {w x y z : V} {f : Hom w x} {g : Hom x y} {h : Hom y z}, comp f (comp g h) = comp (comp f g) h

infix:300 " ⟶ " => Category.Hom
prefix:320 "𝟙 " => Category.id
infixl:300 " ≫ " => Category.comp

attribute [simp] Category.id_comp Category.comp_id

instance : Category (Type u) where
  Hom x y := x → y
  id x := _root_.id
  comp f g := Function.comp g f
  id_comp {x y f} := by simp [Function.comp_def]
  comp_id {x y f} := by simp [Function.comp_def]
  assoc {w x y z f g h} := by simp [Function.comp_def]

variable {C : Type u} [Category.{u, v} C] {X Y : C} in
section

structure Isomorphism (X Y : C) where
  morphism : X ⟶ Y
  inverse : Y ⟶ X
  forward : morphism ≫ inverse = 𝟙 X
  backward : inverse ≫ morphism = 𝟙 Y
infix:100 " ≅ " => Isomorphism

attribute [simp] Isomorphism.forward Isomorphism.backward

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

def Isomorphic (f : X ⟶ Y) : Prop := ∃ (g : Y ⟶ X), f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

@[simp]
theorem Isomorphism.isomorphic (f : X ≅ Y) : Isomorphic f.morphism := by
  exists f.inverse
  simp [f.forward, f.backward]

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
theorem Isomorphism.isomorphic_inv (f : X ≅ Y) : Isomorphic f.inverse := by
  have := f.symm.isomorphic
  simp [Isomorphism.symm] at this
  apply this

class Groupoid (C : Type u) extends Category C where
  iso {X Y : C} (f : X ⟶ Y) : Isomorphic f

@[ext]
structure SliceUnder (c : C) : Type max u v where
  var : C
  hom : c ⟶ x

abbrev SliceUnderHom {c : C} (f g : SliceUnder c) :=
  { h : f.var ⟶ g.var // f.hom ≫ h = g.hom }

@[ext]
structure SliceOver (c : C) : Type max u v where
  var : C
  hom : x ⟶ c

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

instance Category.opposite [inst : Category C] : Category (Opposite C) where
  Hom x y := inst.Hom y.unop x.unop
  id x := inst.id x.unop
  comp {x y z} f g := inst.comp g f
  assoc {w x y z} f g h := by simp; rw [inst.assoc]

example {c : C} (f : X ≅ Y) : (c ⟶ X) ≃ (c ⟶ Y) := by
  let toFun : (c ⟶ X) → (c ⟶ Y) := fun α => α ≫ f.morphism
  let invFun : (c ⟶ Y) → (c ⟶ X) := fun α => α ≫ f.inverse
  apply Equiv.mk toFun invFun
  . intro p
    simp [toFun, invFun, ← Category.assoc]
  . intro p
    simp [toFun, invFun, ← Category.assoc]

def Monic (f : X ⟶ Y) := ∀ ⦃W : C⦄ (g h : W ⟶ X), g ≫ f = h ≫ f → g = h

def Epic (f : X ⟶ Y) := ∀ ⦃Z : C⦄ (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

theorem Isomorphic.monic_and_epic {f : X ⟶ Y} : Isomorphic f → Monic f ∧ Epic f := by
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

theorem Isomorphism.monic_and_epic (f : X ≅ Y) : Monic f.morphism ∧ Epic f.morphism := f.isomorphic.monic_and_epic

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
  intro h1
  intro W α β h2
  apply h1
  simp [Category.assoc, h2]

theorem Monomorphism.monic_of_comp {f : X ↣ Y} {g : X ⟶ W} {h : W ⟶ Y} : f.toFun = g ≫ h → Monic g := by
  intro h1
  apply Monic.of_comp (g := h)
  simp [← h1, f.monic]

/--
Monomorphisms are precisely injections for sets/types.
-/
example {X Y : Type} {f : X ⟶ Y} : Function.Injective f ↔ Monic f := by
  constructor
  . intro h1 W g h h2
    funext x
    apply h1 (funext_iff.mp h2 x)
  . intro h1 x y h2
    simp [Monic] at h1
    simp [Category.Hom, Category.comp] at h1
    let g : Fin 2 → X := fun t => if t = 0 then x else y
    let h : Fin 2 → X := fun t => if t = 0 then y else x
    have : f ∘ g = f ∘ h := by
      funext t
      simp [g, h]
      split
      . exact h2
      . exact h2.symm
    have := h1 g h this
    have conf := funext_iff.mp this 0
    simp [g, h] at conf
    exact conf

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
