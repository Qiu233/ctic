import Ctic.Limit

namespace CTIC

structure Representation [Category.{u, v + 1} C] (F : C ⥤ Type v) where
  obj : C
  iso : HomCov obj ≅ F

class inductive Representable [Category.{u, v + 1} C] (F : C ⥤ Type v) : Prop where
  | intro (rep : Nonempty (Representation F))

notation:max "Hom[" x ", " "-" "]" => HomCov x
notation:max "Hom[" x ", " y "]" => Functor.obj Hom[x, -] y
-- notation:max "Hom[" "-" ", " "-" "]" => HomCov

theorem NatTrans.naturality_expanded_set_valued
    [Category C] {F G : C ⥤ Type v} {α : F ⟹ G} {X Y : C} (f : X ⟶ Y) :
    ∀ u, G.map f (α.eta X u) = α.eta Y (F.map f u) := by
  rw [← funext_iff]
  rw [← Function.comp_def]
  rw [← Function.comp_def]
  exact α.naturality f

namespace Yoneda

abbrev t1 [Category.{u, v + 1} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) → (F x) := fun η => η.eta x (𝟙 x)

abbrev t2 [Category.{u, v + 1} C] (F : C ⥤ Type v) (x : C) : (F x) → (Hom[x, -] ⟹ F) := by
  intro Fx
  letI t (y : C) : Hom[x, y] ⟶ F y := fun f => by
    exact F.map f Fx
  use t
  intro X Y f
  simp [t]
  simp [HomCov]
  simp [Category.comp]
  funext u
  simp [t]
  simp [Category.comp]

def equiv [Category.{u, v + 1} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) ≃ (F x) where
  toFun := t1 F x
  invFun := t2 F x
  right_inv := by
    intro Y
    simp [t1, t2]
    simp [Category.id]
  left_inv := by
    intro α
    simp [t2, t1]
    ext v
    congr
    ext y f
    clear v
    simp [HomCov] at f
    have := α.naturality (X := x) (Y := y) f
    simp [Category.comp] at this
    simp [HomCov] at this
    have := funext_iff.mp this (𝟙 x)
    simp at this
    rw [this]

def iso [Category.{v, v + 1} C] (F : C ⥤ Type v) (x : C) : (Hom[x, -] ⟹ F) ≅ (F x) where
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

def yoneda_factor_x [Category.{v, v + 1} C] (F : C ⥤ Type v) : C ⥤ Type v where
  obj x := Hom[x, -] ⟹ F
  map {X Y} f := by
    simp
    intro T
    let t : (Z : C) → Hom[Y, Z] ⟶ F.obj Z := by
      intro Z g
      apply T.eta
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

def natural_in_x [Category.{v, v + 1} C] (F : C ⥤ Type v) : yoneda_factor_x F ≅ F where
  morphism := by
    use fun x => (Yoneda.iso F x).morphism
    intro X Y f
    simp [Category.comp]
    funext t
    simp
    simp [Yoneda.iso, t1, yoneda_factor_x]
    have := t.naturality_expanded_set_valued f
    simp [HomCov, Category.comp] at this
    simp [this]
  inverse := by
    use fun x => (Yoneda.iso F x).inverse
    intro X Y f
    simp [Category.comp]
    funext t
    simp
    simp [Yoneda.iso, t1, yoneda_factor_x]
    simp [Category.comp]
  forward := by
    simp [Category.id, NatTrans.id]
    simp [Category.comp, NatTrans.comp]
    congr
    funext X t
    simp [Yoneda.iso, t2, t1]
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
    simp [Yoneda.iso, t2, t1]
    simp [Category.id]

def factor_F [Category.{v, v + 1} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
  obj F := Hom[c, -] ⟹ F
  map {G H} α := by
    intro F
    constructor
    case eta =>
      intro X h
      let t := F.eta X h
      exact α.eta X t
    case naturality =>
      intro X Y f
      simp
      funext h
      simp [Category.comp]
      have := α.naturality_expanded_set_valued f (F.eta X h)
      rw [this]
      have := F.naturality_expanded_set_valued f h
      rw [this]

def functor_app_factor_func [Category.{v, v + 1} C] (c : C) : (C ⥤ Type v) ⥤ Type v where
  obj F := F.obj c
  map {G H} α := by
    intro o
    exact α.eta _ o

def natural_in_F [Category.{v, v + 1} C] (c : C) : factor_F c ≅ functor_app_factor_func c where
  morphism := by
    simp [factor_F, functor_app_factor_func]
    constructor
    case eta =>
      simp
      intro F η
      exact η.eta _ (𝟙 c)
    case naturality =>
      simp
      intro X Y f
      funext η
      simp [Category.comp]
  inverse := by
    simp [factor_F, functor_app_factor_func]
    constructor
    case eta =>
      simp
      intro F o
      constructor
      case eta =>
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

def CovEmbedding (C : Type u) [Category.{u, v + 1} C] : Cᵒᵖ ⥤ (C ⥤ Type v) where
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

def Faithful [Category.{u, v + 1} C] : (Yoneda.CovEmbedding C).Faithful := by
  intro X Y f g h1
  simp [Yoneda.CovEmbedding] at h1
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

def Full [Category.{u, u + 1} C] : (Yoneda.CovEmbedding C).Full := by
  intro ⟨X⟩ ⟨Y⟩
  simp [Yoneda.CovEmbedding]
  intro g
  simp [Category.Hom]
  conv =>
    rhs
    intro a
    rw [NatTrans.ext_iff]
    simp
  let f1 := Yoneda.iso (Hom[Y, -]) X
  let f2 := f1.morphism g
  use f2
  simp [f2, f1]
  simp [Yoneda.iso, t1]
  funext c h
  have := g.naturality_expanded_set_valued h (𝟙 X)
  simp [HomCov] at this
  exact this

def FullyFaithful [Category.{u, u + 1} C] : (Yoneda.CovEmbedding C).FullyFaithful := ⟨Yoneda.Full, Yoneda.Faithful⟩

end Yoneda
