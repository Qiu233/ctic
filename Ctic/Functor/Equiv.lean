import Ctic.Functor.NatTrans
namespace CTIC

structure Category.Equivalence (C D : Type*) [Category C] [Category D] where
  F : C ⥤ D
  G : D ⥤ C
  η' : 𝟭 C ≅ F.comp G
  ε' : G.comp F ≅ 𝟭 D

infix:300 " ≌ " => Category.Equivalence

def Skeletal (C : Type u) [Category C] := ∀ (X Y : C), X ≅ Y → X = Y

/-- `SkeletonOf C D` indicates `C` is the skeleton of `D` -/
class SkeletonOf (C : Type u) (D : Type v) [Category C] [Category D] where
  skeletal : Skeletal C
  equiv : C ≌ D

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

theorem Functor.FullyFaithful.bijective {C D : Type*} [Category C] [Category D] {F : C ⥤ D} (ff : Functor.FullyFaithful F) :
    ∀ ⦃X Y : C⦄, Function.Bijective (F.map (X := X) (Y := Y)) := fun X Y => ⟨ff.right (X := X) (Y := Y), ff.left (X := X) (Y := Y)⟩

noncomputable def Functor.FullyFaithful.inv
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} (ff : FullyFaithful F) {X Y : C} (f : F X ⟶ F Y) : X ⟶ Y := ff.left f |>.choose

@[simp]
theorem Functor.FullyFaithful.map_inv
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} (ff : FullyFaithful F) {X Y : C} (f : F X ⟶ F Y) : F.map (ff.inv f) = f := ff.left f |>.choose_spec

theorem Functor.FullyFaithful.inv_unique
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} (ff : FullyFaithful F) {X Y : C} (f : F X ⟶ F Y) : ∀ (r : X ⟶ Y), F.map r = f → r = ff.inv f := by
  intro r h
  simp [inv]
  have := ff.right (X := X) (Y := Y) (a₁ := r) (a₂ := ff.inv f)
  rw [ff.map_inv f] at this
  exact this h

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
    simp [← Category.assoc]
  . intro f
    simp [lemma_1_5_10.i, Isomorphism.symm]
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
  simp [← Category.assoc]

end

theorem HomEquiv.id [Category C] {a b : C} {f : a ⟶ b} : HomEquiv (Isomorphism.id a) (Isomorphism.id b) f = f := by simp [HomEquiv, lemma_1_5_10.i, Isomorphism.id]

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
    simp [-Category.assoc]
    apply faithful
    simp [-Category.assoc]
    let t1 := full ((surj FX).snd.morphism ≫ (Ff ≫ Fg) ≫ (surj FZ).snd.inverse)
    let t2 := full ((surj FX).snd.morphism ≫ Ff ≫ (surj FY).snd.inverse)
    let t3 := full ((surj FY).snd.morphism ≫ Fg ≫ (surj FZ).snd.inverse)
    rw [t1.choose_spec, t2.choose_spec, t3.choose_spec]
    simp [Category.assoc]

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

theorem Functor.FullyFaithful.reflects {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {X Y : C} {f : X ⟶ Y} : F.FullyFaithful → Invertible (F.map f) → Invertible f := by
  intro ff
  intro ⟨g, hg⟩
  simp [Invertible]
  have := ff.left (X := Y) (Y := X) g
  use this.choose
  apply And.intro
  . apply ff.right
    simp [this.choose_spec, hg]
  . apply ff.right
    simp [this.choose_spec, hg]

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
      simp [← Functor.map_comp]
    . simp [NatTrans.comp, t1, Category.id, NatTrans.id, Category.comp]
      congr
      funext X
      simp [Functor.id]
      simp [Category.assoc]
      simp [← Functor.map_comp]
      rw [Category.comp_id (y := F2.obj (G2.obj X))]
      simp
