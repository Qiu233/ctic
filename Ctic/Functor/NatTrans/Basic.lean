import Ctic.Functor.Basic
namespace CTIC

/--
  X ---> F X ---> G X
  |       |        |
f |       |F f     | G f
  |       |        |
  Y ---> F Y ---> G Y
-/
@[ext]
structure NatTrans {C : Type u} {D : Type v} [Category.{p} C] [Category.{q} D] (F G : C ⥤ D) where
  component : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y : C}, ∀ f : X ⟶ Y, component X ≫ G.map f = F.map f ≫ component Y

infix:300 " ⟹ " => NatTrans

instance [Category C] [Category D] {F G : C ⥤ D} : CoeFun (F ⟹ G) (fun _ => ∀ X : C, F.obj X ⟶ G.obj X) where
  coe f := f.component

open Lean in
@[app_unexpander NatTrans.component]
private def unexpand_NatTrans_component : PrettyPrinter.Unexpander
  | `($(_) $f $a) => `($f $a)
  | _ => throw ()

abbrev NatTrans.id {C : Type u} {D : Type v} [Category C] [Category D] (F : C ⥤ D) : F ⟹ F where
  component X := 𝟙 (F.obj X)
  naturality {X Y} f := by simp

abbrev NatTrans.comp [Category C] [Category D] {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H where
  component X := α.component X ≫ β.component X
  naturality {X Y} f := by
    simp
    rw [← Category.assoc]
    simp [β.naturality]
    simp [α.naturality]

theorem NatTrans.assoc [Category C] [Category D] {F G H J : C ⥤ D} {α : F ⟹ G} {β : G ⟹ H} {γ : H ⟹ J} : α.comp (β.comp γ) = (α.comp β).comp γ := by
  simp [NatTrans.comp]

@[simp]
theorem NatTrans.id_comp [Category C] [Category D] {F G : C ⥤ D} {α : F ⟹ G} : (NatTrans.id F).comp α = α := by
  simp [NatTrans.comp, NatTrans.id]

@[simp]
theorem NatTrans.comp_id [Category C] [Category D] {F G : C ⥤ D} {α : F ⟹ G} : α.comp (NatTrans.id G) = α := by
  simp [NatTrans.comp, NatTrans.id]

instance [Category C] [Category D] : Category (C ⥤ D) where
  Hom X Y := NatTrans X Y
  id X := NatTrans.id X
  comp := NatTrans.comp
  assoc := NatTrans.assoc
  id_comp := NatTrans.id_comp
  comp_id := NatTrans.comp_id
