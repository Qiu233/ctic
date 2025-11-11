import Ctic.Limit

namespace CTIC

variable {C : Type u}
variable [Category.{v, u} C]

@[ext]
structure Algebra (F : C ⥤ C) where
  A : C
  α : F A ⟶ A

@[ext]
structure Algebra.Hom {F : C ⥤ C} (X Y : Algebra F) where
  morphism : X.A ⟶ Y.A
  prop : X.α ≫ morphism = F.map morphism ≫ Y.α

instance (F : C ⥤ C) : Category (Algebra F) where
  Hom := Algebra.Hom
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, by
    rw [Category.assoc, f.2]
    rw [← Category.assoc, g.2]
    aesop
    ⟩
  id X := ⟨𝟙 X.1, by aesop⟩
  id_comp := by aesop
  comp_id := by aesop
  assoc {W X Y Z} f g h := by
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    obtain ⟨h, hh⟩ := h
    dsimp
    congr 1
    aesop

protected def Algebra.lift (F : C ⥤ C) : Algebra F ⥤ Algebra F where
  obj X := ⟨F X.A, F.map X.α⟩
  map {X Y} f := by
    obtain ⟨X, α⟩ := X
    obtain ⟨Y, β⟩ := Y
    use F.map f.morphism
    rw [← Functor.map_comp]
    rw [f.prop]
    aesop
  map_id {X} := by simp [Category.id]
  map_comp {X Y Z} f g := by simp [Category.comp]

def Algebra.iso_of_initial {F : C ⥤ C} {X : Algebra F} (h : Initial X) : (Algebra.lift F) X ≅ X where
  morphism := by
    simp [Algebra.lift]
    constructor
    case morphism => exact X.α
    case prop => simp
  inverse := by
    simp [Algebra.lift]
    constructor
    case morphism =>
      let t := h.morphism ((Algebra.lift F) X)
      exact t.morphism
    case prop =>
      simp [Algebra.lift]
      let t := h.morphism ((Algebra.lift F) X)
      change X.α ≫ t.morphism = F.map t.morphism ≫ F.map X.α
      rw [t.prop]
      congr 1
  forward := by
    simp [Category.id, Category.comp]
    congr 1
    let t := h.morphism ((Algebra.lift F) X)
    rw [t.prop]
    simp [Algebra.lift]
    rw [← Functor.map_comp]
    rw [← Functor.map_id]
    congr 1
    have := t.prop
    simp [Algebra.lift] at this
    let s : Algebra.Hom X X := ⟨t.morphism ≫ X.α, by rw [Functor.map_comp, ← this, Category.assoc]⟩
    have h1 := h.unique (f := s)
    have h2 := h.self
    have h3 := Eq.trans h1 h2
    rw [Algebra.Hom.ext_iff] at h3
    dsimp [s] at h3
    rw [h3]
    simp [Category.id]
  backward := by
    simp [Category.id, Category.comp]
    congr 1
    let t := h.morphism ((Algebra.lift F) X)
    change t.morphism ≫ X.α = 𝟙 X.A
    have := t.prop
    simp [Algebra.lift] at this
    let s : Algebra.Hom X X := ⟨t.morphism ≫ X.α, by rw [Functor.map_comp, ← this, Category.assoc]⟩
    have h1 := h.unique (f := s)
    have h2 := h.self
    have h3 := Eq.trans h1 h2
    rw [Algebra.Hom.ext_iff] at h3
    dsimp [s] at h3
    rw [h3]
    simp [Category.id]

def Algebra.iso_of_initial' {F : C ⥤ C} {X : Algebra F} (h : Initial X) : F X.A ≅ X.A where
  morphism := (X.iso_of_initial h).morphism.morphism
  inverse := (X.iso_of_initial h).inverse.morphism
  forward := by
    have := (X.iso_of_initial h).forward
    simp [Category.comp, Algebra.lift, Category.id] at this
    rw [Algebra.Hom.ext_iff] at this
    simp at this
    exact this
  backward := by
    have := (X.iso_of_initial h).backward
    simp [Category.comp, Algebra.lift, Category.id] at this
    rw [Algebra.Hom.ext_iff] at this
    simp at this
    exact this

def Nat.functor : Type ⥤ Type where
  obj X := Unit ⊕ X
  map {X Y} f v := v.rec Sum.inl (Sum.inr ∘ f)
  map_id {X} := by
    funext t
    cases t <;> aesop
  map_comp {X Y Z} f g := by
    funext t
    cases t <;> aesop

def Nat.Alg : Algebra Nat.functor where
  A := ℕ
  α {X} := X.rec (λ _ ↦ 0) Nat.succ

def Nat.Alg.Initial : Initial Nat.Alg where
  morphism X := by
    use fun n => n.rec (X.α (.inl ())) (λ _ ih => X.α (.inr ih))
    simp [Category.comp]
    funext n
    cases n with
    | inl u => cases u; rfl
    | inr n => exact n.rec (by rfl) (λ _ _ => by rfl)
  unique {Y} := by
    intro ⟨f, hf⟩
    congr 1
    simp [Nat.Alg, Nat.functor, Category.comp] at hf
    rw [funext_iff] at hf
    funext n
    induction n with
    | zero => apply hf (.inl ())
    | succ n ih =>
      have := hf (.inr n)
      simp at this
      simp at hf
      rw [this]
      simp
      apply congrArg
      apply congrArg
      exact ih
