import Ctic.Functor.NatTrans.Basic
namespace CTIC

def Isomorphism.component [Category C] [Category D] {F G : C ⥤ D} (iso : F ≅ G) (X : C) : F.obj X ≅ G.obj X := by
  apply Isomorphism.mk (iso.morphism.component X) (iso.inverse.component X)
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

def Isomorphism.of_component [Category C] [Category D] {F G : C ⥤ D}
    (η : ∀ (X : C), F.obj X ≅ G.obj X)
    (natural : ∀ {X Y : C} (f : X ⟶ Y), (η X).morphism ≫ G.map f = F.map f ≫ (η Y).morphism) : F ≅ G where
  morphism := ⟨fun x => η x, natural⟩
  inverse := ⟨fun x => (η x).inverse, by
    intro X Y f
    simp
    apply (η X).epic
    simp
    apply (η Y).monic
    simp [← Category.assoc]
    symm
    apply natural
    ⟩
  forward := by simp [Category.comp, NatTrans.comp]; rfl
  backward := by simp [Category.comp, NatTrans.comp]; rfl

def Isomorphism.component_eta [Category C] [Category D] {F G : C ⥤ D} (iso : F ≅ G) :
    Isomorphism.of_component iso.component iso.morphism.naturality = iso := by
  simp [of_component]
  rw [Isomorphism.ext_iff]
  simp
  rw [NatTrans.ext_iff]
  simp
  rfl

@[simp]
theorem Isomorphism.component_def [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : (iso.component X).morphism = iso.morphism.component X := by simp [Isomorphism.component]

@[simp]
theorem Isomorphism.component_inv [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X : C} : (iso.component X).inverse = iso.inverse.component X := by simp [Isomorphism.component]

@[simp]
lemma Category.fuse_middle_right {C : Type u} [Category C] {X1 X2 X3 X4 X5 : C} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3} {f3 : X3 ⟶ X4} {f4 : X4 ⟶ X5} :
  f1 ≫ (f2 ≫ (f3 ≫ f4)) = f1 ≫ (f2 ≫ f3) ≫ f4 := by simp [Category.assoc]

@[simp]
lemma Category.fuse_middle_left {C : Type u} [Category C] {X1 X2 X3 X4 X5 : C} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3} {f3 : X3 ⟶ X4} {f4 : X4 ⟶ X5} :
  f1 ≫ f2 ≫ f3 ≫ f4 = f1 ≫ (f2 ≫ f3) ≫ f4 := by simp [Category.assoc]

@[simp]
lemma Isomorphism.forward_iso [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} (X : C) : iso.morphism.component X ≫ iso.inverse.component X = 𝟙 (F.obj X) := by
  have := iso.forward
  simp [Category.comp, NatTrans.comp] at this
  rw [NatTrans.ext_iff] at this
  simp at this
  rw [funext_iff] at this
  apply this

@[simp]
lemma Isomorphism.backward_iso [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} (X : C) : iso.inverse.component X ≫ iso.morphism.component X = 𝟙 (G.obj X) := by
  have := iso.backward
  simp [Category.comp, NatTrans.comp] at this
  rw [NatTrans.ext_iff] at this
  simp at this
  rw [funext_iff] at this
  apply this

lemma Isomorphism.component_epic [Category C] [Category D] {F G : C ⥤ D} {f f' : G.obj X ⟶ A} {iso : F ≅ G} : iso.morphism.component X ≫ f = iso.morphism.component X ≫ f' → f = f' := fun h1 => (iso.component X).epic f f' h1

lemma Isomorphism.component_monic [Category C] [Category D] {F G : C ⥤ D} {f f' : A ⟶ F.obj X} {iso : F ≅ G} : f ≫ iso.morphism.component X = f' ≫ iso.morphism.component X → f = f' := fun h1 => (iso.component X).monic f f' h1

lemma Isomorphism.component_inv_epic [Category C] [Category D] {F G : C ⥤ D} {f f' : F.obj X ⟶ A} {iso : F ≅ G} : iso.inverse.component X ≫ f = iso.inverse.component X ≫ f' → f = f' := fun h1 => (iso.component X).symm.epic f f' h1

lemma Isomorphism.component_inv_monic [Category C] [Category D] {F G : C ⥤ D} {f f' : A ⟶ G.obj X} {iso : F ≅ G} : f ≫ iso.inverse.component X = f' ≫ iso.inverse.component X → f = f' := fun h1 => (iso.component X).symm.monic f f' h1

theorem NatTrans.epic_of_components_epic [Category C] [Category D] {F G : C ⥤ D} (α : F ⟹ G) : (∀ X, Epic (α X)) → Epic (C := C ⥤ D) α := by
  intro h1 H g h h2
  simp [Epic] at h1
  rw [NatTrans.ext_iff]
  funext X
  apply h1
  simp [Category.comp, NatTrans.comp] at h2
  rw [NatTrans.ext_iff, funext_iff] at h2
  apply h2

theorem NatTrans.monic_of_components_monic [Category C] [Category D] {F G : C ⥤ D} (α : F ⟹ G) : (∀ X, Monic (α X)) → Monic (C := C ⥤ D) α := by
  intro h1 H g h h2
  simp [Monic] at h1
  rw [NatTrans.ext_iff]
  funext X
  apply h1
  simp [Category.comp, NatTrans.comp] at h2
  rw [NatTrans.ext_iff, funext_iff] at h2
  apply h2

theorem NatTrans.isic_of_components_isic [Category C] [Category D] {F G : C ⥤ D} (α : F ⟹ G) : (∀ X, Invertible (α X)) → Invertible (C := C ⥤ D) α := by
  intro h1
  let t (X) : G X ⟶ F X := (h1 X).choose
  let s : G ⟹ F := {
      component := t,
      naturality := by
        intro X Y f
        have := (h1 X).choose_spec
        simp [t]
        have ⟨_, e⟩ := (h1 X).monic_and_epic
        apply e
        simp [this]
        have ⟨m, _⟩ := (h1 Y).monic_and_epic
        apply m
        rw [← Category.assoc]
        have := (h1 Y).choose_spec
        rw [this.2]
        simp [α.naturality]
        }

  simp [Invertible]
  use s
  apply And.intro
  . simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext x
    simp [s, t]
    have := (h1 x).choose_spec
    simp [this]
  . simp [Category.comp, NatTrans.comp, Category.id, NatTrans.id]
    congr
    funext x
    simp [s, t]
    have := (h1 x).choose_spec
    simp [this]

def Invertible.of_bijective_of_sets {X Y : Type u} [DecidableEq Y] {f : X ⟶ Y} (bij : Function.Bijective f) : Invertible f := by
  let t := Equiv.ofBijective f bij
  use t.invFun
  apply And.intro
  . have := t.left_inv
    dsimp [Function.LeftInverse] at this
    funext x
    apply this
  . have := t.right_inv
    dsimp [Function.LeftInverse] at this
    funext x
    apply this

def Invertible.of_monic_and_epic_of_sets {X Y : Type u} [DecidableEq Y] {f : X ⟶ Y} (monic : Monic f) (epic : Epic f) : Invertible f := by
  rw [Function.Monic_iff_Injective] at monic
  rw [Function.Epic_iff_Surjective] at epic
  apply Invertible.of_bijective_of_sets ⟨monic, epic⟩
