import Ctic.Limit.Basic

namespace CTIC

namespace Yoneda.Notation

scoped notation:max "Hom[" x ", " "-" "]" => HomCov xᵒᵖ
scoped notation:max "Hom[" x ", " y "]" => Functor.obj Hom[x, -] y
scoped notation:max "Hom[" "-" ", " x "]" => HomCon x

scoped notation:max "Hom[" F "(" "-" ")" ", " Y "]" => Fᵒᵖ ⋙ Hom[-, Y]
scoped notation:max "Hom[" X ", " F "(" "-" ")" "]" => F ⋙ Hom[X, -]

end Yoneda.Notation

namespace Yoneda
open Lean Notation

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

end Yoneda

open Yoneda.Notation in
section
@[simp]
theorem HomCon.comp_obj_def [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] { unop := X } = Hom[F X, Y] := by rfl

@[simp]
theorem HomCon.comp_obj_def' [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : D} :
    Hom[F(-), Y] Xᵒᵖ = Hom[F X, Y] := by rfl

@[simp]
theorem Functor.op_map_def [Category C] [Category D] {F : C ⥤ D} {X : C} {Y : C} {f : X ⟶ Y} :
    Fᵒᵖ.map f = F.map f := by rfl
end

theorem NatTrans.naturality_expanded_set_valued
    [Category C] {F G : C ⥤ Type v} {α : F ⟹ G} {X Y : C} (f : X ⟶ Y) :
    ∀ u, G.map f (α.component X u) = α.component Y (F.map f u) := by
  rw [← funext_iff]
  rw [← Function.comp_def]
  rw [← Function.comp_def]
  exact α.naturality f

namespace Yoneda
open Notation

namespace Covariant

abbrev t1.{v, u} [Category.{v, u} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) → ULift.{u, v} (F x) :=
  fun η => ⟨η.component x (𝟙 x)⟩

abbrev t2.{v, u} [Category.{v, u} C] (F : C ⥤ Type v) (x : C) : ULift.{u, v} (F x) → (Hom[x, -] ⟹ F) := by
  intro ⟨Fx⟩
  letI t (y : C) : Hom[x, y] ⟶ F y := fun f => by
    exact F.map f Fx
  use t
  intro X Y f
  simp [t]
  simp [Category.comp]
  funext u
  simp
  simp [Category.comp]

def iso.{v, u} [Category.{v, u} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) ≅ ULift.{u, v} (F x) where
  morphism := t1 F x
  inverse := t2 F x
  forward := by
    simp [Category.comp]
    funext α
    simp [t1, t2]
    ext v
    congr
    ext y f
    clear v
    have := α.naturality_expanded_set_valued f (𝟙 x)
    simp at this
    exact this
  backward := by
    simp [Category.comp]
    funext ⟨Y⟩
    simp [t1, t2]
    congr

def yoneda_factor_x [Category.{u} C] (F : C ⥤ Type u) : C ⥤ Type u where
  obj x := Hom[x, -] ⟹ F
  map {X Y} f := by
    intro T
    let t : (Z : C) → Hom[Y, Z] ⟶ F.obj Z := by
      intro Z g
      apply T.component
      exact (f ≫ g)
    use t
    intro U V g
    simp [t]
    simp [Category.comp]
    simp [HomCov]
    funext s
    simp
    exact T.naturality_expanded_set_valued g (f ≫ s)
  map_id := by
    intro X
    simp [Category.id]
    funext t
    simp
  map_comp := by
    intro X Y Z f g
    simp [Category.comp]
    funext t
    simp

def natural_in_x.{u} [Category.{u} C] (F : C ⥤ Type u) : yoneda_factor_x F ≅ F where
  morphism := by
    use fun x => (iso F x).morphism ≫ ULift.down
    intro X Y f
    simp [Category.comp]
    funext t
    simp
    simp [iso, t1, yoneda_factor_x]
    have := t.naturality_expanded_set_valued f
    simp [HomCov, Category.comp] at this
    simp [this]
  inverse := by
    use fun x => ULift.up ≫ (iso F x).inverse
    intro X Y f
    simp [Category.comp]
    funext t
    simp
    simp [iso, t1, yoneda_factor_x]
    simp [Category.comp]
  forward := by
    simp [Category.id, NatTrans.id]
    simp [Category.comp, NatTrans.comp]
    congr
    funext X t
    simp [iso, t2, t1]
    congr
    funext c f
    have := t.naturality_expanded_set_valued f
    simp [HomCov, Category.comp] at this
    simp [this]
  backward := by
    simp [Category.id, NatTrans.id]
    simp [Category.comp, NatTrans.comp]
    congr
    funext X FX
    simp
    simp [iso, t2, t1]
    simp [Category.id]

def factor_F [Category.{v} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
  obj F := Hom[c, -] ⟹ F
  map {G H} α := by
    intro F
    constructor
    case component =>
      intro X h
      let t := F.component X h
      exact α.component X t
    case naturality =>
      intro X Y f
      simp
      funext h
      simp [Category.comp]
      have := α.naturality_expanded_set_valued f (F.component X h)
      rw [this]
      have := F.naturality_expanded_set_valued f h
      rw [this]

def functor_app_factor_func [Category.{v} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
  obj F := F.obj c
  map {G H} α := by
    intro o
    exact α.component _ o

def natural_in_F [Category.{v} C] (c : C) : factor_F c ≅ functor_app_factor_func c where
  morphism := by
    simp [factor_F, functor_app_factor_func]
    constructor
    case component =>
      simp
      intro F η
      exact η.component _ (𝟙 c)
    case naturality =>
      simp
      intro X Y f
      funext η
      simp [Category.comp]
  inverse := by
    simp [factor_F, functor_app_factor_func]
    constructor
    case component =>
      simp
      intro F o
      constructor
      case component =>
        intro Y f
        exact F.map f o
      case naturality =>
        intro X Y f
        simp [Category.comp, HomCov]
        funext g
        simp [Category.comp]
    case naturality =>
      intro F G η
      simp [Category.comp]
      funext t
      simp
      funext u f
      have := η.naturality_expanded_set_valued f
      simp at this
      rw [this]
  forward := by
    simp [Category.comp, NatTrans.comp]
    rw [NatTrans.ext_iff]
    funext t
    simp [Category.id]
    funext η
    simp
    rw [NatTrans.ext_iff]
    simp
    funext Y f
    have := η.naturality_expanded_set_valued f (𝟙 c)
    simp [this, HomCov]
  backward := by
    simp [Category.comp, NatTrans.comp]
    rw [NatTrans.ext_iff]
    funext t
    simp [Category.id]
    funext η
    simp [Category.id]

def Embedding.{v, u} {C : Type u} [Category.{v, u} C] : Cᵒᵖ ⥤ (C ⥤ Type v) where
  obj X := Hom[X.unop, -]
  map {X Y} f := by
    simp [Category.Hom]
    let t : (c : C) → (Hom[X.unop, c] → Hom[Y.unop, c]) := by
      intro c
      simp [HomCov]
      intro h
      let f' : Y.unop ⟶ X.unop := f
      exact f' ≫ h
    use t
    intro U V g
    simp [HomCov, Category.comp]
    funext x
    simp [t]
  map_id := by
    intro ⟨X⟩
    simp [Category.id, NatTrans.id]
    congr
  map_comp := by
    intro X Y Z f g
    simp [Category.comp, NatTrans.comp]
    congr
    funext _ _
    simp

def Faithful.{v, u} [Category.{v, u} C] : (Embedding (C := C)).Faithful := by
  intro X Y f g h1
  simp [Embedding] at h1
  rw [NatTrans.ext_iff] at h1
  simp at h1
  rw [funext_iff] at h1
  conv at h1 =>
    intro x
    rw [funext_iff]
    intro h
  specialize h1 (X.unop) (𝟙 X.unop)
  simp at h1
  exact h1

def Full.{v, u} [Category.{v, u} C] : (Embedding (C := C)).Full := by
  intro ⟨X⟩ ⟨Y⟩
  simp [Embedding]
  intro g
  simp [Category.Hom]
  conv =>
    rhs
    intro a
    rw [NatTrans.ext_iff]
    simp
  let f2 := t1 Hom[Y, -] X g
  use f2.down
  simp [f2]
  funext c h
  have := g.naturality_expanded_set_valued h (𝟙 X)
  simp [HomCov] at this
  exact this

def FullyFaithful [Category.{v, v} C] : (Embedding (C := C)).FullyFaithful := ⟨Full, Faithful⟩

end Covariant

namespace Contravariant

abbrev t1.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : (Hom[-, x] ⟹ F) ⟶ ULift.{u, v} (F xᵒᵖ) :=
  fun η => ⟨η.component xᵒᵖ (𝟙 x)⟩

abbrev t2.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (y : C) : ULift.{u, v} (F yᵒᵖ) ⟶ (Hom[-, y] ⟹ F) := by
  intro ⟨Fx⟩
  letI t (x : Cᵒᵖ) : Hom[xᵒᵖ, y] ⟶ F x := fun f => by
    exact F.map f Fx
  use t
  intro X Y f
  simp [t]
  simp [Category.comp]
  funext u
  simp [t]
  change F.map f (F.map u Fx) = F.map (u ≫ f) Fx
  rw [Functor.map_comp]
  simp [Category.comp]

def iso.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : (Hom[-, x] ⟹ F) ≅ ULift.{u, v} (F xᵒᵖ) where
  morphism := t1 F x
  inverse := t2 F x
  forward := by
    simp [Category.comp]
    funext α
    simp [t1, t2]
    ext v
    congr
    ext y f
    clear v
    have := α.naturality_expanded_set_valued f (𝟙 x)
    simp [HomCov] at this
    exact this
  backward := by
    simp [Category.comp]
    funext ⟨Y⟩
    simp [t1, t2]
    congr
    change F.map (𝟙 xᵒᵖ) Y = (𝟙 F xᵒᵖ) Y
    rw [Functor.map_id]

theorem monic_t1 [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : Monic (t1 F x) := (iso F x).monic

theorem epic_t1 [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : Epic (t1 F x) := (iso F x).epic

theorem monic_t2 [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : Monic (t2 F x) := (iso F x).symm.monic

theorem epic_t2 [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : Epic (t2 F x) := (iso F x).symm.epic

def Embedding.{v, u} {C : Type u} [Category.{v, u} C] : C ⥤ (Cᵒᵖ ⥤ Type v) where
  obj X := Hom[-, X]
  map {X Y} f := by
    simp [Category.Hom]
    let t : (c : Cᵒᵖ) → (Hom[c.unop, X] → Hom[c.unop, Y]) := by
      intro c
      simp [HomCov]
      intro h
      exact h ≫ f
    use t
    intro U V g
    simp [HomCov, Category.comp]
    funext x
    simp [t]

def Faithful.{v, u} [Category.{v, u} C] : (Embedding (C := C)).Faithful := by
  intro X Y f g h1
  simp [Embedding] at h1
  rw [NatTrans.ext_iff] at h1
  simp at h1
  rw [funext_iff] at h1
  conv at h1 =>
    intro x
    rw [funext_iff]
    intro h
  specialize h1 (Xᵒᵖ) (𝟙 Xᵒᵖ)
  simp [Category.id] at h1
  exact h1

def Full.{v, u} [Category.{v, u} C] : (Embedding (C := C)).Full := by
  intro X Y
  simp [Embedding]
  intro g
  simp [Category.Hom]
  conv =>
    rhs
    intro a
    rw [NatTrans.ext_iff]
    simp
  let f2 := t1 Hom[-, Y] X g
  use f2.down
  simp [f2]
  funext c h
  have := g.naturality_expanded_set_valued h (𝟙 X)
  simp [HomCov] at this
  exact this

def FullyFaithful [Category.{u} C] : (Embedding (C := C)).FullyFaithful := ⟨Full, Faithful⟩

end Contravariant

end Yoneda

end CTIC
