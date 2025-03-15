import Ctic.Limit

namespace CTIC

notation:max "Hom[" x ", " "-" "]" => HomCov xᵒᵖ
notation:max "Hom[" x ", " y "]" => Functor.obj Hom[x, -] y
notation:max "Hom[" "-" ", " x "]" => HomCon x

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

theorem NatTrans.naturality_expanded_set_valued
    [Category C] {F G : C ⥤ Type v} {α : F ⟹ G} {X Y : C} (f : X ⟶ Y) :
    ∀ u, G.map f (α.component X u) = α.component Y (F.map f u) := by
  rw [← funext_iff]
  rw [← Function.comp_def]
  rw [← Function.comp_def]
  exact α.naturality f

namespace Yoneda

namespace Covariant

abbrev t1 [Category.{u, v + 1} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) → (F x) :=
  fun η => η.component x (𝟙 x)

abbrev t2 [Category.{u, v + 1} C] (F : C ⥤ Type v) (x : C) : (F x) → (Hom[x, -] ⟹ F) := by
  intro Fx
  letI t (y : C) : Hom[x, y] ⟶ F y := fun f => by
    exact F.map f Fx
  use t
  intro X Y f
  simp [t]
  simp [Category.comp]
  funext u
  simp [t]
  simp [Category.comp]

def iso [Category.{u} C] (F : C ⥤ Type u) (x : C) : (Hom[x, -] ⟹ F) ≅ (F x) where
  morphism := t1 F x
  inverse := t2 F x
  forward := by
    simp [Category.comp]
    funext α
    simp [t2, t1]
    ext v
    congr
    ext y f
    clear v
    simp [HomCov] at f
    have := α.naturality_expanded_set_valued f (𝟙 x)
    simp [HomCov] at this
    exact this
  backward := by
    simp [Category.comp]
    funext Y
    simp [t1, t2]

def yoneda_factor_x [Category.{u} C] (F : C ⥤ Type u) : C ⥤ Type u where
  obj x := Hom[x, -] ⟹ F
  map {X Y} f := by
    simp
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

def natural_in_x [Category.{u} C] (F : C ⥤ Type u) : yoneda_factor_x F ≅ F where
  morphism := by
    use fun x => (iso F x).morphism
    intro X Y f
    simp [Category.comp]
    funext t
    simp
    simp [iso, t1, yoneda_factor_x]
    have := t.naturality_expanded_set_valued f
    simp [HomCov, Category.comp] at this
    simp [this]
  inverse := by
    use fun x => (iso F x).inverse
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

def factor_F [Category.{v, v + 1} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
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

def functor_app_factor_func [Category.{v, v + 1} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
  obj F := F.obj c
  map {G H} α := by
    intro o
    exact α.component _ o

def natural_in_F [Category.{v, v + 1} C] (c : C) : factor_F c ≅ functor_app_factor_func c where
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

def Embedding (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ (C ⥤ Type u) where
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
    intro X
    simp [Category.id, NatTrans.id]
    congr
  map_comp := by
    intro X Y Z f g
    simp [Category.comp, NatTrans.comp]
    congr
    funext _ _
    simp

def Faithful [Category.{u} C] : (Embedding C).Faithful := by
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

def Full [Category.{u} C] : (Embedding C).Full := by
  intro ⟨X⟩ ⟨Y⟩
  simp [Embedding]
  intro g
  simp [Category.Hom]
  conv =>
    rhs
    intro a
    rw [NatTrans.ext_iff]
    simp
  let f1 := iso (Hom[Y, -]) X
  let f2 := f1.morphism g
  use f2
  simp [f2, f1]
  simp [iso, t1]
  funext c h
  have := g.naturality_expanded_set_valued h (𝟙 X)
  simp [HomCov] at this
  exact this

def FullyFaithful [Category.{u} C] : (Embedding C).FullyFaithful := ⟨Full, Faithful⟩

end Covariant

namespace Contravariant

abbrev t1 [Category.{u, v + 1} C] (F : Cᵒᵖ ⥤ Type v) (x : C) : (Hom[-, x] ⟹ F) → (F xᵒᵖ) :=
  fun η => η.component xᵒᵖ (𝟙 x)

abbrev t2 [Category.{u, v + 1} C] (F : Cᵒᵖ ⥤ Type v) (y : C) : (F yᵒᵖ) → (Hom[-, y] ⟹ F) := by
  intro Fx
  letI t (x : Cᵒᵖ) : Hom[xᵒᵖ, y] ⟶ F x := fun f => by
    exact F.map f Fx
  use t
  intro X Y f
  simp [t]
  simp [Category.comp]
  funext u
  simp [t]
  simp [HasOpposite.op]
  change yᵒᵖ ⟶ X at u
  change F.map f (F.map u Fx) = F.map (u ≫ f) Fx
  rw [Functor.map_comp]
  simp [Category.comp]

def iso [Category.{u} C] (F : Cᵒᵖ ⥤ Type u) (x : C) : (Hom[-, x] ⟹ F) ≅ (F xᵒᵖ) where
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
    simp [HomCov] at f
    have := α.naturality_expanded_set_valued f (𝟙 x)
    simp [HomCov] at this
    exact this
  backward := by
    simp [Category.comp]
    funext Y
    simp [t1, t2]
    change F.map (𝟙 xᵒᵖ) Y = (𝟙 F xᵒᵖ) Y
    rw [Functor.map_id]

def Embedding (C : Type u) [Category.{u} C] : C ⥤ (Cᵒᵖ ⥤ Type u) where
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

def Faithful [Category.{u} C] : (Embedding C).Faithful := by
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
  simp at h1
  exact h1

def Full [Category.{u} C] : (Embedding C).Full := by
  intro X Y
  simp [Embedding]
  intro g
  simp [Category.Hom]
  conv =>
    rhs
    intro a
    rw [NatTrans.ext_iff]
    simp
  let f1 := iso (Hom[-, Y]) X
  let f2 := f1.morphism g
  use f2
  simp [f2, f1]
  simp [iso, t1]
  funext c h
  have := g.naturality_expanded_set_valued h (𝟙 X)
  simp [HomCov] at this
  exact this

def FullyFaithful [Category.{u} C] : (Embedding C).FullyFaithful := ⟨Full, Faithful⟩

end Contravariant

end Yoneda

structure RepresentationCov [Category.{u} C] (F : C ⥤ Type u) where
  obj : C
  iso : HomCov objᵒᵖ ≅ F

structure RepresentationContra [Category.{u} C] (F : Cᵒᵖ ⥤ Type u) where
  obj : C
  iso : HomCon obj ≅ F

class inductive RepresentableCov [Category.{u} C] (F : C ⥤ Type u) : Prop where
  | intro (rep : Nonempty (RepresentationCov F))

class inductive RepresentableContra [Category.{u} C] (F : Cᵒᵖ ⥤ Type u) : Prop where
  | intro (rep : Nonempty (RepresentationContra F))

variable {C : Type u}
variable [Category.{u} C]
variable {F : Cᵒᵖ ⥤ Type u}

abbrev CategoryOfElements (F : Cᵒᵖ ⥤ Type u) :=  Comma (Yoneda.Contravariant.Embedding C) (TrivialFunctor F)

prefix:max "∫ " => CategoryOfElements

lemma Yoneda.isic_of_terminal_in_category_of_elements
    [decEq : ∀ X, DecidableEq (F X)] {L : CategoryOfElements F} (terminal : Terminal L) : Invertible L.f := by
  obtain ⟨c, u, α⟩ := L
  change Hom[-, c] ⟶ F at α
  apply NatTrans.isic_of_components_isic
  intro X
  simp
  apply Invertible.of_monic_and_epic_of_sets
  . rw [Function.Monic_iff_Injective]
    intro f g h1
    change Xᵒᵖ ⟶ c at f g
    let s : CategoryOfElements F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.iso F Xᵒᵖ |>.inverse ((α.component X) f)⟩
    let t : CategoryOfElements F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.iso F Xᵒᵖ |>.inverse ((α.component X) g)⟩
    let p := terminal.morphism s
    let q := terminal.morphism t
    have h2 : s = t := by simp [s, t]; rw [h1]
    have h3 : p.k = q.k := by
      simp [p, q]
      congr
    have h5 : ((Yoneda.Contravariant.Embedding C).map f ≫ α) = (Yoneda.Contravariant.iso F Xᵒᵖ).inverse (α.component X f) := by
      have := (Yoneda.Contravariant.iso F Xᵒᵖ).monic
      rw [Function.Monic_iff_Injective] at this
      apply this
      rw [← Function.comp_apply (f := (Yoneda.Contravariant.iso F Xᵒᵖ).morphism)]
      rw [← Function.comp_apply (f := (Yoneda.Contravariant.iso F Xᵒᵖ).morphism)]
      have : (Yoneda.Contravariant.iso F Xᵒᵖ).morphism ∘ (Yoneda.Contravariant.iso F Xᵒᵖ).inverse = 𝟙 (F X) := by
        funext t
        change F.map (𝟙 X) t = (𝟙 F X) t
        rw [Functor.map_id]
      rw [this]
      simp [Category.id, Yoneda.Contravariant.iso, Yoneda.Contravariant.Embedding, Yoneda.Contravariant.t1, Category.comp]
      change (α.component X) (𝟙 X ≫ f) = (α.component X) f
      simp
    have h6 := p.commu
    change s.f = (Yoneda.Contravariant.Embedding C).map p.k ≫ α at h6
    have h7 := terminal.unique (X := s) (f := ⟨f, (), h5.symm⟩)
    have h8 : f = p.k := by
      rw [CommaHom.ext_iff] at h7
      simp at h7
      simp [h7]
    have h10 : ((Yoneda.Contravariant.Embedding C).map g ≫ α) = (Yoneda.Contravariant.iso F Xᵒᵖ).inverse (α.component X g) := by
      have := (Yoneda.Contravariant.iso F Xᵒᵖ).monic
      rw [Function.Monic_iff_Injective] at this
      apply this
      rw [← Function.comp_apply (f := (Yoneda.Contravariant.iso F Xᵒᵖ).morphism)]
      rw [← Function.comp_apply (f := (Yoneda.Contravariant.iso F Xᵒᵖ).morphism)]
      have : (Yoneda.Contravariant.iso F Xᵒᵖ).morphism ∘ (Yoneda.Contravariant.iso F Xᵒᵖ).inverse = 𝟙 (F X) := by
        funext t
        change F.map (𝟙 X) t = (𝟙 F X) t
        rw [Functor.map_id]
      rw [this]
      simp [Category.id, Yoneda.Contravariant.iso, Yoneda.Contravariant.Embedding, Yoneda.Contravariant.t1, Category.comp]
      change (α.component X) (𝟙 X ≫ g) = (α.component X) g
      simp
    have h11 := q.commu
    change t.f = (Yoneda.Contravariant.Embedding C).map q.k ≫ α at h11
    have h12 := terminal.unique (X := t) (f := ⟨g, (), h10.symm⟩)
    have h13 : g = q.k := by
      rw [CommaHom.ext_iff] at h12
      simp at h12
      simp [h12]
    rw [h8, h13]
    exact h3
  . rw [Function.Epic_iff_Surjective]
    intro e
    change F X at e
    let s : CategoryOfElements F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.iso F Xᵒᵖ |>.inverse e⟩
    have h1 : s.f.component X (𝟙 X) = e := by
      simp [s, Yoneda.Contravariant.iso]
      change (F.map (𝟙 X)) e = e
      rw [Functor.map_id (X := X)]
      simp [Category.id]
    let t := terminal.morphism s
    have h2 := t.commu
    change s.f = (Yoneda.Contravariant.Embedding C).map t.k ≫ α at h2
    have h3 : (α.component X) t.k = s.f.component X (𝟙 X) := by
      rw [h2]
      simp [Yoneda.Contravariant.Embedding]
      simp [Category.comp]
    have h4 := Eq.trans h3 h1
    use t.k

theorem Yoneda.terminal_in_category_of_elements_of_isic {L : CategoryOfElements F} (isic : Invertible L.f) : Nonempty (Terminal L) := by
  refine Nonempty.intro ⟨?morphism, ?unique⟩
  case morphism =>
    intro X
    let t : Hom[-, X.d] ⟶ Hom[-, L.d] := X.f ≫ isic.choose
    use (Yoneda.Contravariant.FullyFaithful (C := C)).inv t, ()
    simp [t]
    have := isic.choose_spec
    rw [← Category.assoc]
    rw [this.2]
    simp
  case unique =>
    intro X f
    obtain ⟨k, h, commu⟩ := f
    simp at commu
    simp
    congr
    apply (Yoneda.Contravariant.FullyFaithful (C := C)).right
    rw [(Yoneda.Contravariant.FullyFaithful (C := C)).map_inv]
    rw [commu]
    rw [← Category.assoc]
    rw [isic.choose_spec.1]
    simp

theorem Yoneda.isic_iff_terminal_in_category_of_elements
    [∀ X, DecidableEq (F X)] (L : CategoryOfElements F) : Nonempty (Terminal L) ↔ Invertible L.f :=
  ⟨fun ⟨ne⟩ => Yoneda.isic_of_terminal_in_category_of_elements ne, Yoneda.terminal_in_category_of_elements_of_isic⟩
