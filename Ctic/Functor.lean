import Ctic.Category
namespace CTIC

structure Functor (C : Type u) (D : Type v) [Category.{u, a} C] [Category.{v, b} D] : Type max u v a b where
  obj : C → D
  map {X Y : C} : X ⟶ Y → obj X ⟶ obj Y
  map_id {X : C} : map (𝟙 X) = 𝟙 (obj X) := by aesop
  map_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : map (f ≫ g) = map f ≫ map g := by aesop

attribute [simp] Functor.map_id Functor.map_comp

infixr:300 " ⥤ " => Functor

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


instance Category.product (C : Type u) (D : Type v) [Category C] [Category D] : Category (C × D) where
  Hom X Y := (X.fst ⟶ Y.fst) × (X.snd ⟶ Y.snd)
  id X := (𝟙 X.fst, 𝟙 X.snd)
  comp {X Y Z} := fun ⟨fc, fd⟩ ⟨gc, gd⟩ => ⟨fc ≫ gc, fd ≫ gd⟩
  assoc {W X Y Z} := by simp [Category.assoc]

/--
  X ---> F X ---> G X
  |       |        |
f |       |F f     | G f
  |       |        |
  Y ---> F Y ---> G Y
-/
@[ext]
structure NatTrans {C : Type u} {D : Type v} [Category C] [Category D] (F G : C ⥤ D) where
  eta : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y : C}, ∀ f : X ⟶ Y, eta X ≫ G.map f = F.map f ≫ eta Y

infix:300 " ⟹ " => NatTrans

abbrev NatTrans.id {C : Type u} {D : Type v} [Category C] [Category D] (F : C ⥤ D) : F ⟹ F where
  eta X := 𝟙 (F.obj X)
  naturality {X Y} f := by simp

abbrev NatTrans.comp [Category C] [Category D] {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H where
  eta X := α.eta X ≫ β.eta X
  naturality {X Y} f := by
    simp
    rw [← Category.assoc]
    simp [β.naturality]
    rw [Category.assoc]
    simp [α.naturality]
    rw [← Category.assoc]

theorem NatTrans.assoc [Category C] [Category D] {F G H J : C ⥤ D} {α : F ⟹ G} {β : G ⟹ H} {γ : H ⟹ J} : α.comp (β.comp γ) = (α.comp β).comp γ := by
  simp [NatTrans.comp]
  funext X
  simp [Category.assoc]

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

def Hom {C : Type u} [Category.{u, v + 1} C] : (Opposite C × C) ⥤ Type v where
  obj := fun (X, Y) => X.unop ⟶ Y
  map {X Y} := fun ⟨f, h⟩ g => f ≫ g ≫ h
  map_id {X} := by
    funext g
    simp [Category.id]
  map_comp {X Y Z f g} := by
    funext h
    simp [Category.comp, Category.assoc]

theorem Functor.iso {C : Type u} {D : Type v} [Category C] [Category D] {F : C ⥤ D} {X Y : C} {f : X ⟶ Y} : Isomorphic f → Isomorphic (F.map f) := by
  intro ⟨i, iso⟩
  use F.map i
  simp [← Functor.map_comp, iso, Functor.map_id]

structure Comma [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E] (F : D ⥤ C) (G : E ⥤ C) : Type max u1 u2 u3 v1 v2 v3 where
  d : D
  e : E
  f : F.obj d ⟶ G.obj e

structure CommaHom [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E] {F : D ⥤ C} {G : E ⥤ C} (X Y : Comma F G) : Type max u1 u2 u3 v1 v2 v3 where
  h : X.d ⟶ Y.d
  k : X.e ⟶ Y.e
  commu : X.f ≫ G.map k = F.map h ≫ Y.f

instance {C D E : Type*} [Category C] [Category D] [Category E] (F : D ⥤ C) (G : E ⥤ C) : Category (Comma F G) where
  Hom X Y := CommaHom X Y
  id X := by
    simp
    apply CommaHom.mk (𝟙 X.d) (𝟙 X.e)
    simp [Functor.map_id]
  comp {X Y Z} := by
    simp
    intro f g
    apply CommaHom.mk (f.h ≫ g.h) (f.k ≫ g.k)
    simp [Functor.map_comp]
    rw [Category.assoc]
    rw [f.commu]
    rw [← Category.assoc]
    rw [g.commu]
    rw [Category.assoc]
  assoc {W X Y Z} f g h := by simp [Category.assoc]

def Functor.const {C D : Type*} [Category C] [Category D] : D ⥤ C ⥤ D where
  obj d := { obj := fun _ => d, map := fun _ => 𝟙 d }
  map {X Y} f := NatTrans.mk (fun _ => f) (by simp)

def Comma.dom [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E] {F : D ⥤ C} {G : E ⥤ C} : Comma F G ⥤ D where
  obj := Comma.d
  map := CommaHom.h

def Comma.cod [Category.{u1, v1} C] [Category.{u2, v2} D] [Category.{u3, v3} E] {F : D ⥤ C} {G : E ⥤ C} : Comma F G ⥤ E where
  obj := Comma.e
  map := CommaHom.k

abbrev over [Category C] (c : C) := Comma (𝟭 C) ((Functor.const (C := C)).obj c)

abbrev under [Category C] (c : C) := Comma ((Functor.const (C := C)).obj c) (𝟭 C)

instance overCat [Category C] (c : C) : Category (over c) := inferInstance
instance underCat [Category C] (c : C) : Category (under c) := inferInstance

structure Category.Equivalence (C D : Type*) [Category C] [Category D] where
  F : C ⥤ D
  G : D ⥤ C
  η' : 𝟭 C ≅ F.comp G
  ε' : G.comp F ≅ 𝟭 D

infix:300 " ≌ " => Category.Equivalence

@[symm]
def Category.Equivalence.symm [Category C] [Category D] (equiv : Category.Equivalence C D) : Category.Equivalence D C where
  F := equiv.G
  G := equiv.F
  η' := equiv.ε'.symm
  ε' := equiv.η'.symm

def Functor.Full {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop := ∀ ⦃X Y : C⦄, Function.Surjective (F.map (X := X) (Y := Y))
def Functor.Faithful {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop := ∀ ⦃X Y : C⦄, Function.Injective (F.map (X := X) (Y := Y))
def Functor.EssentiallySurjective {C D : Type*} [Category C] [Category D] (F : C ⥤ D) := ∀ d : D, Σ' c : C, F.obj c ≅ d
def Functor.EssentiallyInjective {C D : Type*} [Category C] [Category D] (F : C ⥤ D) := ∀ X Y : C, F.obj X ≅ F.obj Y → X ≅ Y
abbrev Functor.FullyFaithful {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop := F.Full ∧ F.Faithful

variable [Category C] {a a' b b' : C} {f : a ⟶ b} {α : a ≅ a'} {β : b ≅ b'} in
section

private def lemma_1_5_10.i (f : a ⟶ b) (α : a ≅ a') (β : b ≅ b') : a' ⟶ b' := α.inverse ≫ f ≫ β.morphism

private lemma lemma_1_5_10.ii : ∀ {f' : a' ⟶ b'}, α.morphism ≫ f' = f ≫ β.morphism → f' = lemma_1_5_10.i f α β := by
  intro f' h1
  simp [lemma_1_5_10.i]
  apply α.monic_and_epic.right (Z := b')
  rw [Category.assoc]
  rw [Category.assoc]
  simp
  exact h1

private lemma lemma_1_5_10.iii : ∀ {f' : a' ⟶ b'}, f' ≫ β.inverse = α.inverse ≫ f → f' = lemma_1_5_10.i f α β := by
  intro f' h1
  simp [lemma_1_5_10.i]
  apply β.symm.monic_and_epic.left (W := a')
  rw [← Category.assoc]
  simp [Isomorphism.symm]
  exact h1

private lemma lemma_1_5_10.iv : ∀ {f' : a' ⟶ b'}, α.morphism ≫ f' ≫ β.inverse = f → f' = lemma_1_5_10.i f α β := by
  intro f' h1
  simp [lemma_1_5_10.i]
  apply α.monic_and_epic.right (Z := b')
  rw [Category.assoc]
  rw [Category.assoc]
  simp
  apply β.symm.monic_and_epic.left (W := a)
  simp [Isomorphism.symm]
  simp [h1]
  rw [← Category.assoc]
  simp

def HomEquiv (α : a ≅ a') (β : b ≅ b') : (a ⟶ b) ≃ (a' ⟶ b') := by
  apply Equiv.mk (lemma_1_5_10.i (α := α) (β := β)) (lemma_1_5_10.i (α := α.symm) (β := β.symm))
  . intro f
    simp [lemma_1_5_10.i, Isomorphism.symm]
    simp [Category.assoc]
    simp [← Category.assoc]
  . intro f
    simp [lemma_1_5_10.i, Isomorphism.symm]
    simp [Category.assoc]
    simp [← Category.assoc]

theorem HomEquiv.def' : ∀ f : a ⟶ b, (HomEquiv α β).toFun f = α.inverse ≫ f ≫ β.morphism := by simp [HomEquiv, lemma_1_5_10.i]

theorem HomEquiv.def : ∀ f : a ⟶ b, HomEquiv α β f = α.inverse ≫ f ≫ β.morphism := by simp [HomEquiv, lemma_1_5_10.i]

theorem HomEquiv.comm_ii : ∀ {f : a ⟶ b}, ∀ {f' : a' ⟶ b'}, α.morphism ≫ f' = f ≫ β.morphism → HomEquiv α β f = f' := by
  intro f f' h1
  simp [HomEquiv, lemma_1_5_10.ii h1]

theorem HomEquiv.comm_iii : ∀ {f : a ⟶ b}, ∀ {f' : a' ⟶ b'}, f' ≫ β.inverse = α.inverse ≫ f → HomEquiv α β f = f' := by
  intro f f' h1
  simp [HomEquiv, lemma_1_5_10.iii h1]

theorem HomEquiv.comm_iv : ∀ {f : a ⟶ b}, ∀ {f' : a' ⟶ b'}, α.morphism ≫ f' ≫ β.inverse = f → HomEquiv α β f = f' := by
  intro f f' h1
  simp [HomEquiv, lemma_1_5_10.iv h1]

theorem HomEquiv.symm : ∀ {f : a ⟶ b}, ∀ {f' : a' ⟶ b'}, HomEquiv α β f = f' → HomEquiv α.symm β.symm f' = f := by
  intro f f' h1
  simp [← h1]
  simp [HomEquiv, lemma_1_5_10.i, Isomorphism.symm]
  simp [Category.assoc]
  simp [← Category.assoc]

end

theorem HomEquiv.id [Category C] {a b : C} {f : a ⟶ b} : HomEquiv (Isomorphism.id a) (Isomorphism.id b) f = f := by simp [HomEquiv, lemma_1_5_10.i, Isomorphism.id]

def Isomorphism.component [Category C] [Category D] {F G : C ⥤ D} (iso : F ≅ G) (X : C) : F.obj X ≅ G.obj X := by
  apply Isomorphism.mk (iso.morphism.eta X) (iso.inverse.eta X)
  . have := iso.forward
    simp [Category.comp, NatTrans.comp] at this
    rw [NatTrans.ext_iff] at this
    simp at this
    rw [funext_iff] at this
    specialize this X
    simp [this, Category.id, NatTrans.id]
  . have := iso.backward
    simp [Category.comp, NatTrans.comp] at this
    rw [NatTrans.ext_iff] at this
    simp at this
    rw [funext_iff] at this
    specialize this X
    simp [this, Category.id, NatTrans.id]

@[simp]
theorem Isomorphism.component_def [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : (iso.component X).morphism = iso.morphism.eta X := by simp [Isomorphism.component]

@[simp]
theorem Isomorphism.component_inv [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : (iso.component X).inverse = iso.inverse.eta X := by simp [Isomorphism.component]

namespace Category

def Equivalence.essentially_surjective {C D : Type*} [Category C] [Category D] (equiv : Category.Equivalence C D) : equiv.F.EssentiallySurjective := by
  obtain ⟨F, G, η, ε⟩ := equiv
  intro d
  use G.obj d
  exact ε.component d

theorem Equivalence.faithful {C D : Type*} [Category C] [Category D] (equiv : Category.Equivalence C D) : equiv.F.Faithful := by
  obtain ⟨F, G, η, ε⟩ := equiv
  intro X Y f f' h1
  simp at h1
  let α := η.component X |>.symm
  let β := η.component Y |>.symm
  simp [Functor.comp, Functor.id] at α β
  have h2 : α.morphism ≫ f = G.map (F.map f) ≫ β.morphism := η.inverse.naturality f
  have h3 : α.morphism ≫ f' = G.map (F.map f') ≫ β.morphism := η.inverse.naturality f'
  have h4 := HomEquiv.comm_ii h2
  have h5 := HomEquiv.comm_ii h3
  simp [← h1] at h5
  rw [← h4, ← h5]

theorem Equivalence.full {C D : Type*} [Category C] [Category D] (equiv : Category.Equivalence C D) : equiv.F.Full := by
  have faithful := equiv.symm.faithful
  obtain ⟨F, G, η, ε⟩ := equiv
  intro X Y h
  simp at h
  simp [Category.Equivalence.symm] at faithful
  simp
  let α := η.component X |>.symm
  let β := η.component Y |>.symm
  let f : X ⟶ Y := HomEquiv α β (G.map h)
  use f
  apply faithful
  apply Eq.trans (Eq.symm (HomEquiv.comm_ii (η.morphism.naturality f))) (HomEquiv.symm (show (HomEquiv α β) (G.map h) = f by simp [f]))

end Category

theorem Functor.FullyFaithful.iff {C D : Type*} [Category C] [Category D] {F : C ⥤ D} : F.FullyFaithful ↔ ∀ (X Y : C), Function.Bijective (F.map (X := X) (Y := Y)) := by
  constructor
  . intro ⟨h1, h2⟩ X Y
    exact ⟨h2 (X := X) (Y := Y), h1 (X := X) (Y := Y)⟩
  . intro h
    apply And.intro
    . intro X Y
      have := h (X := X) (Y := Y)
      simp [this.surjective]
    . intro X Y
      have := h (X := X) (Y := Y)
      simp [this.injective]

noncomputable def Functor.FullyFaithful.essentially_injective {C D : Type*} [Category C] [Category D] {F : C ⥤ D} : F.FullyFaithful → F.EssentiallyInjective := by
  intro ⟨full, faithful⟩
  intro X Y iso
  simp [Functor.Full] at full
  simp [Functor.Faithful] at faithful
  have t1 := full iso.morphism
  have t2 := full iso.inverse
  apply Isomorphism.mk t1.choose t2.choose
  . apply faithful
    simp [t1.choose_spec, t2.choose_spec]
  . apply faithful
    simp [t1.choose_spec, t2.choose_spec]

private noncomputable def invFunctor {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (full : F.Full) (faithful : F.Faithful) (surj : F.EssentiallySurjective) : D ⥤ C where
  obj d := (surj d).fst
  map {FX FY} Ff := (full ((surj FX).snd.morphism ≫ Ff ≫ (surj FY).snd.inverse)).choose
  map_id {FX} := by
    let t := full ((surj FX).snd.morphism ≫ 𝟙 FX ≫ (surj FX).snd.inverse)
    apply faithful
    rw [t.choose_spec]
    simp
  map_comp {FX FY FZ Ff Fg} := by
    simp
    apply faithful
    simp
    let t1 := full ((surj FX).snd.morphism ≫ (Ff ≫ Fg) ≫ (surj FZ).snd.inverse)
    let t2 := full ((surj FX).snd.morphism ≫ Ff ≫ (surj FY).snd.inverse)
    let t3 := full ((surj FY).snd.morphism ≫ Fg ≫ (surj FZ).snd.inverse)
    rw [t1.choose_spec, t2.choose_spec, t3.choose_spec]
    simp [Category.assoc]
    conv =>
      rhs
      lhs
      lhs
      rw [← Category.assoc]
      simp

@[simp]
private lemma invFunctor_obj {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {X : D}
    (full : F.Full) (faithful : F.Faithful) (surj : F.EssentiallySurjective) : (invFunctor full faithful surj).obj X = (surj X).fst := by
  simp [invFunctor]

@[simp]
private lemma invFunctor_map_spec {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {X Y : D} {f' : X ⟶ Y}
    (full : F.Full) (faithful : F.Faithful) (surj : F.EssentiallySurjective) : F.map ((invFunctor full faithful surj).map f') = (surj X).snd.morphism ≫ f' ≫ (surj Y).snd.inverse := by
  simp [invFunctor]
  let t := full ((surj X).snd.morphism ≫ f' ≫ (surj Y).snd.inverse)
  rw [t.choose_spec]

noncomputable def Category.Equivalence.of_fully_faithful_essentially_surjective {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (full : F.Full) (faithful : F.Faithful) (surj : F.EssentiallySurjective) : Category.Equivalence C D where
  F := F
  G := invFunctor full faithful surj
  η' := by
    let eta1 := fun X => full ((surj (F.obj X)).snd).inverse
    let eta2 := fun X => full ((surj (F.obj X)).snd).morphism
    constructor
    case morphism =>
      use fun x => eta1 x |>.choose
      intro X Y f
      apply faithful
      simp [Functor.comp, Functor.id]
      simp [(eta1 X).choose_spec, (eta1 Y).choose_spec]
      simp [Category.assoc]
    case inverse =>
      use fun x => eta2 x |>.choose
      intro X Y f
      apply faithful
      simp [Functor.comp, Functor.id]
      simp [(eta2 X).choose_spec, (eta2 Y).choose_spec]
      simp [← Category.assoc]
    case forward =>
      simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
      congr 1
      funext X
      apply faithful
      simp [(eta1 X).choose_spec, (eta2 X).choose_spec]
    case backward =>
      simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
      congr 1
      funext X
      apply faithful
      simp [(eta1 X).choose_spec, (eta2 X).choose_spec]
  ε' := by
    let eta1 := fun X => (surj X).snd.morphism
    let eta2 := fun X => (surj X).snd.inverse
    constructor
    case morphism =>
      use eta1
      intro X Y f
      simp [Functor.id, Functor.comp, eta1]
      simp [← Category.assoc]
    case inverse =>
      use eta2
      intro X Y f
      simp [Functor.id, Functor.comp, eta2]
      simp [Category.assoc]
    case forward =>
      simp [Category.id, NatTrans.id, Category.comp, NatTrans.comp]
      congr
      funext X
      simp [Functor.comp]
      simp [eta1, eta2]
    case backward =>
      simp [Category.id, NatTrans.id, Category.comp, NatTrans.comp]
      congr
      funext X
      simp [Functor.comp]
      simp [eta1, eta2]

theorem Functor.FullyFaithful.reflects {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {X Y : C} {f : X ⟶ Y} : F.FullyFaithful → Isomorphic (F.map f) → Isomorphic f := by
  intro ff
  intro ⟨g, hg⟩
  simp [Isomorphic]
  have := ff.left (X := Y) (Y := X) g
  use this.choose
  apply And.intro
  . apply ff.right
    simp [this.choose_spec, hg]
  . apply ff.right
    simp [this.choose_spec, hg]

-- def IsoRel {C : Type u} [Category C] (X Y : C) : Prop := Nonempty (X ≅ Y)

-- namespace IsoRel

-- variable {C : Type u} [Category C]

-- @[simp]
-- theorem refl (X : C) : IsoRel X X := Nonempty.intro (Isomorphism.id X)
-- @[symm]
-- theorem symm {X Y : C} : IsoRel X Y → IsoRel Y X := fun iso => Nonempty.intro iso.some.symm
-- @[trans]
-- theorem trans {X Y Z : C} : IsoRel X Y → IsoRel Y Z → IsoRel X Z := fun h1 h2 => Nonempty.intro (Isomorphism.comp h1.some h2.some)

-- instance setoid : Setoid C where
--   r := IsoRel
--   iseqv := { refl := refl, symm := symm, trans := trans }

-- end IsoRel

def Skeletal (C : Type u) [Category C] := ∀ (X Y : C), X ≅ Y → X = Y

/-- `SkeletonOf C D` indicates `C` is the skeleton of `D` -/
class SkeletonOf (C : Type u) (D : Type v) [Category C] [Category D] where
  skeletal : Skeletal C
  equiv : Category.Equivalence C D

def Category.Discrete (C : Type u) [Category C] := ∀ (X Y : C), X ⟶ Y → X = Y

class Category.EssentiallyDiscrete (C : Type u) [Category C] where
  D : Type v
  [cat : Category D]
  [disc : Discrete D]
  [equiv : Category.Equivalence C D]

def Category.Equivalence.id (C : Type u) [Category C] : C ≌ C where
  F := 𝟭 C
  G := 𝟭 C
  η' := by
    simp
    apply Isomorphism.mk (NatTrans.id _) (NatTrans.id _)
      <;> simp [Category.comp, Category.id]
  ε' := by
    simp
    apply Isomorphism.mk (NatTrans.id _) (NatTrans.id _)
      <;> simp [Category.comp, Category.id]

@[simp]
lemma Category.fuse_middle_right {C : Type u} [Category C] {X1 X2 X3 X4 X5 : C} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3} {f3 : X3 ⟶ X4} {f4 : X4 ⟶ X5} :
  f1 ≫ (f2 ≫ (f3 ≫ f4)) = f1 ≫ (f2 ≫ f3) ≫ f4 := by simp [Category.assoc]

@[simp]
lemma Category.fuse_middle_left {C : Type u} [Category C] {X1 X2 X3 X4 X5 : C} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3} {f3 : X3 ⟶ X4} {f4 : X4 ⟶ X5} :
  f1 ≫ f2 ≫ f3 ≫ f4 = f1 ≫ (f2 ≫ f3) ≫ f4 := by simp [Category.assoc]

@[simp]
lemma Isomorphism.forward_iso [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : iso.morphism.eta X ≫ iso.inverse.eta X = 𝟙 (F.obj X) := by
  have := iso.forward
  simp [Category.comp, NatTrans.comp] at this
  rw [NatTrans.ext_iff] at this
  simp at this
  rw [funext_iff] at this
  apply this

@[simp]
lemma Isomorphism.backward_iso [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : iso.inverse.eta X ≫ iso.morphism.eta X = 𝟙 (G.obj X) := by
  have := iso.backward
  simp [Category.comp, NatTrans.comp] at this
  rw [NatTrans.ext_iff] at this
  simp at this
  rw [funext_iff] at this
  apply this

def Category.Equivalence.comp {C D E : Type*} [Category C] [Category D] [Category E] (α : C ≌ D) (β : D ≌ E) : C ≌ E where
  F := α.F.comp β.F
  G := β.G.comp α.G
  η' := by
    obtain ⟨F1, G1, η1, ε1⟩ := α
    obtain ⟨F2, G2, η2, ε2⟩ := β
    simp [Functor.assoc]
    let t1 : NatTrans (F1 ⋙ G1) (F1 ⋙ F2 ⋙ G2 ⋙ G1) := by
      use fun X => G1.map (η2.component (F1.obj X)).morphism
      intro X Y f
      simp [Functor.comp]
      simp [← Functor.map_comp]
      congr 1
      exact η2.morphism.naturality (F1.map f)
    let t2 : NatTrans (F1 ⋙ F2 ⋙ G2 ⋙ G1) (F1 ⋙ G1) := by
      use fun X => G1.map (η2.component (F1.obj X)).inverse
      intro X Y f
      simp [Functor.comp]
      simp [← Functor.map_comp]
      congr 1
      exact η2.inverse.naturality (F1.map f)
    apply Isomorphism.mk (η1.morphism.comp t1) (t2.comp η1.inverse)
    . simp [NatTrans.comp, t1, Category.id, NatTrans.id, Category.comp]
      congr
      funext X
      simp [Functor.id]
      simp [Category.assoc]
      simp [← Functor.map_comp]
      rw [Category.comp_id (y := G1.obj (F1.obj X))]
      simp
    . simp [NatTrans.comp, t1, Category.id, NatTrans.id, Category.comp]
      congr
      funext X
      simp [Functor.id, Functor.comp]
      simp [Category.assoc]
      simp [← Functor.map_comp]
  ε' := by
    obtain ⟨F1, G1, η1, ε1⟩ := α
    obtain ⟨F2, G2, η2, ε2⟩ := β
    simp [Functor.assoc]
    let t1 : NatTrans (G2 ⋙ G1 ⋙ F1 ⋙ F2) (G2 ⋙ F2) := by
      use fun X => F2.map (ε1.component (G2.obj X)).morphism
      intro X Y f
      simp [Functor.comp]
      simp [← Functor.map_comp]
      congr 1
      exact ε1.morphism.naturality (G2.map f)
    let t2 : NatTrans (G2 ⋙ F2) (G2 ⋙ G1 ⋙ F1 ⋙ F2) := by
      use fun X => F2.map (ε1.component (G2.obj X)).inverse
      intro X Y f
      simp [Functor.comp]
      simp [← Functor.map_comp]
      congr 1
      exact ε1.inverse.naturality (G2.map f)
    apply Isomorphism.mk (t1.comp ε2.morphism) (ε2.inverse.comp t2)
    . simp [NatTrans.comp, t1, Category.id, NatTrans.id, Category.comp]
      congr
      funext X
      simp [Functor.id, Functor.comp]
      simp [Category.assoc]
      simp [← Functor.map_comp]
    . simp [NatTrans.comp, t1, Category.id, NatTrans.id, Category.comp]
      congr
      funext X
      simp [Functor.id]
      simp [Category.assoc]
      simp [← Functor.map_comp]
      rw [Category.comp_id (y := F2.obj (G2.obj X))]
      simp
