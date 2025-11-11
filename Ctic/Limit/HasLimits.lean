import Ctic.Limit.Basic
import Ctic.Limit.Diagram
import Ctic.Repre.Contravariant
import Ctic.Repre.Notation

namespace CTIC

abbrev HasLimit {J C : Type*} [Category J] [Category C] (F : J ⥤ C) : Prop := Nonempty (Limit F)

class HasLimitsOfShape (C J : Type*) [Category C] [Category J] : Prop where
  limits : ∀ (F : J ⥤ C), HasLimit F

class HasFiniteProducts (C : Type u) [Category C] : Prop where
  proj : ∀ (n : ℕ), HasLimitsOfShape C (Discrete (Fin n))

open Diagram in
abbrev HasTerminal (C : Type*) [Category C] : Prop := HasLimitsOfShape C 𝟬

example : HasTerminal Type where
  limits F := by
    apply Nonempty.intro
    let c : Cone F := ⟨Unit, ⟨(fun x y => by exfalso; apply Diagram.Nullary.empty x), by intro X Y f; exfalso; apply Diagram.Nullary.empty X⟩⟩
    use c
    apply Terminal.mk
    case morphism =>
      intro ⟨L, π⟩
      simp [c]
      simp [Category.Hom]
      use fun _ => ()
      intro j
      exfalso
      apply Diagram.Nullary.empty j
    case unique_morphism =>
      intro L f
      simp
      congr

open Diagram in
noncomputable def HasTerminal.terminal {C : Type*} [Category C] [has_terminal : HasTerminal C] : C := by
  let F : 𝟬 ⥤ C := by
    refine ⟨(fun x => by exfalso; apply Nullary.empty x), fun f => by simp; exact 𝟙 _, ?_, ?_⟩
    . intro X
      simp
    . intro X Y Z f g
      simp
  have has_limit := has_terminal.limits F
  let t := has_limit.some
  exact t.L.N

class HasFiniteLimitsOf.{u, v, u_1, u_2} (C : Type u) [Category.{u_1, u} C] (n : ℕ) : Prop where
  proj : ∀ (J : Type v) [Category J], (Fin n ≃ J) → HasLimitsOfShape.{u, v, u_1, u_2} C J

class HasFiniteLimits.{u, v, u_1, u_2} (C : Type u) [Category.{u_1, u} C] : Prop where
  proj : ∀ (n : ℕ), HasFiniteLimitsOf.{u, v, u_1, u_2} C n

inductive Centered (α : Type u) where
  | peri (a : α)
  | center

instance [Category α] : Category (Centered α) where
  Hom X Y := by
    match X, Y with
    | .peri x, .peri y => exact Category.Hom x y
    | .peri x, .center => exact PUnit
    | .center, .center => exact PUnit
    | .center, .peri _ => exact PEmpty
  id X := by
    match X with
    | .peri X => exact 𝟙 X
    | .center => exact PUnit.unit
  comp {X Y Z} f g := by
    match X, Y, Z with
    | .peri X, .peri Y, .peri Z => simp at f g; simp; exact f ≫ g
    | .peri X, _, .center => simp; exact PUnit.unit
    | .center, .center, .center => simp; exact PUnit.unit
  id_comp {X Y} f := by
    match X, Y with
    | .peri x, .peri y => simp
    | .peri x, .center => simp
    | .center, .center => simp
  comp_id {X Y} f := by
    match X, Y with
    | .peri x, .peri y => simp
    | .peri x, .center => simp
    | .center, .center => simp
  assoc {W X Y Z} f g h := by
    match W, X, Y, Z with
    | .peri W, .peri X, .peri Y, .peri Z => simp
    | .peri W, .peri X, _, .center => simp
    | .peri W, .center, .center, .center => simp
    | .center, .center, .center, .center => simp

def Centered.add_equiv : (Fin n ≃ α) → (Fin (n + 1) ≃ Centered α) := by
  intro equiv
  let f : Fin (n + 1) → Centered α := fun x =>
    if h : x = n then .center
    else .peri (equiv.toFun ⟨x.val, by have := Nat.le_of_lt_add_one x.isLt; apply Nat.lt_of_le_of_ne this h⟩)
  let g : Centered α → Fin (n + 1) := fun x =>
    match x with
    | .peri x => ⟨(equiv.invFun x).val, by have := (equiv.invFun x).isLt; apply Nat.lt_add_right _ this⟩
    | .center => ⟨n, by simp⟩
  refine ⟨f, g, ?_, ?_⟩
  . intro x
    simp [g, f]
    if h : x = n then
      rw [dif_pos h]
      simp
      congr
      simp [h]
    else
      rw [dif_neg h]
      simp
  . intro x
    dsimp [f]
    split
    . rename_i h
      simp [g] at h
      split at h
      . simp at h
        rename_i a
        have : equiv.symm a ≥ n := by simp [h]
        have : equiv.symm a < n := by simp
        aesop
      . rfl
    . rename_i h
      simp [g] at h
      cases x with
      | center => simp at h
      | peri x' => simp [g]

example (C : Type u) [SmallCategory.{u} C] [has_finite_limits : HasFiniteLimitsOf.{u, v, u, u'} C (n + 1)] (X : C) : HasFiniteLimitsOf.{u, v, u, u'} (SliceOver X) n := by
  constructor
  intro J _ equiv
  let equiv' := Centered.add_equiv equiv
  have ⟨h⟩ := has_finite_limits.proj (Centered J) equiv'
  constructor
  intro F
  let G : Centered J ⥤ C := by
    -- constructor
    let u : Centered J → C := fun x =>
      match x with
      | .center => X
      | .peri x => (F.obj x).var
    use u
    . intro x y f
      simp [u]
      match x, y with
      | .center, .center => exact 𝟙 X
      | .peri x, .peri y =>
        simp
        change x ⟶ y at f
        exact (F.map f).val
      | .peri x, .center =>
        simp
        exact (F.obj x).hom
    . simp
      intro x
      cases x with
      | center => simp [u]
      | peri x' =>
        simp [u]
        -- rw [F.map_id (X := x')]
        let g : x' ⟶ x' := 𝟙 Centered.peri x'
        change (F.map g).val = 𝟙 (F x').var
        have : g = 𝟙 x' := by
          rfl
        rw [this]
        rw [F.map_id]
        congr
    . intro x y z f g
      simp
      match x, y, z with
      | .peri x, .peri y, .peri z =>
        simp
        change x ⟶ y at f
        change y ⟶ z at g
        change (F.map (f ≫ g)).val = (F.map f).val ≫ (F.map g).val
        rw [F.map_comp]
        congr
      | .peri x, .peri y, .center =>
        change x ⟶ y at f
        simp
        rw [(F.map f).prop]
      | .peri x, .center, .center =>
        simp
        rw [Category.comp_id]
      | .center, .center, .center =>
        simp
        rw [Category.id_comp]
  have forward : ∀ L : Limit F, ∃ L' : Limit G, L.L.N.var = L'.L.N := by
    intro ⟨⟨⟨L, p⟩, π⟩, h⟩
    simp
    let cone : Cone G := by
      use L
      constructor
      case component =>
        intro x
        simp
        match x with
        | .peri x' => exact π.component x' |>.val
        | .center => exact p
      case naturality =>
        intro x y f
        simp
        match x, y with
        | .peri x', .peri y' =>
          simp
          change (π.component x').val ≫ G.map f = 𝟙 L ≫ (π.component y').val
          rw [Category.id_comp]
          have := π.naturality f
          simp at this
          change π.component x' ≫ F.map f = 𝟙 { var := L, hom := p : SliceOver X } ≫ π.component y' at this
          rw [Category.id_comp] at this
          rw [← this]
          congr
        | .peri x', .center =>
          simp
          change (π.component x').val ≫ G.map f = 𝟙 L ≫ p
          rw [Category.id_comp]
          simp [G]
          rw [(π.component x').prop]
          congr
        | .center, .center =>
          simp [G]
          change p = 𝟙 L ≫ p
          simp
    let L' : Limit G := by
      use cone
      constructor
      case morphism =>
        intro c
        let c' : Cone F := by
          let s : SliceOver X := by
            use c.N
            exact c.π'.component .center
          use s
          constructor
          case component =>
            intro x
            simp
            use c.π'.component (.peri x)
            simp [s]
            have := c.π'.naturality (X := .peri x) (Y := .center) (PUnit.unit)
            simp [G] at this
            rw [this]
            change 𝟙 c.N ≫ _ = _
            simp
          case naturality =>
            intro x y f
            simp
            change _ ≫ _ = 𝟙 s ≫ _
            simp
            simp [Category.comp]
            congr
            change Centered.peri x ⟶ Centered.peri y at f
            have := c.π'.naturality f
            simp [G] at this
            rw [this]
            change 𝟙 _ ≫ _ = _
            simp
        constructor
        case u => exact h.morphism c' |>.u.val
        case universal =>
          intro x
          simp [cone]
          match x with
          | .center =>
            simp
            rw [h.morphism c' |>.u.prop]
          | .peri x' =>
            simp
            have := h.morphism c' |>.universal x'
            simp at this
            simp [Category.comp] at this
            conv at this => rhs; simp [c']
            rw [Subtype.eq_iff] at this
            simp at this
            exact this
      case unique_morphism =>
        intro c ⟨f, h'⟩
        congr
        let s : SliceOver X := { var := c.N, hom := c.π'.component Centered.center }
        let component : (x : J) → (Δ s) x ⟶ F x := by
          intro x
          simp
          let t := c.π'.component (Centered.peri x)
          use t
          simp [t]
          have := c.π'.naturality (X := .peri x) (Y := .center) (PUnit.unit)
          simp [G] at this
          rw [this]
          change 𝟙 _ ≫ _ = _
          simp
          rfl
        have naturality : ∀ {X Y : J} (f : X ⟶ Y), component X ≫ F.map f = (Δ s).map f ≫ component Y := by
          intro x y f
          simp
          change _ = 𝟙 _ ≫ _
          simp [component]
          simp [Category.comp]
          congr
          change Centered.peri x ⟶ Centered.peri y at f
          have := c.π'.naturality f
          simp [G] at this
          rw [this]
          change 𝟙 _ ≫ _ = _
          simp
        let c' : Cone F := { N := s, π' := { component, naturality } }
        change f = (h.morphism c').u.val
        -- have := h.unique_morphism
        let f' : c' ⟶ { N := { var := L, hom := p }, π' := π } := by
          constructor
          case u =>
            simp [c', s]
            constructor
            case val => use f
            simp
            have := h' .center
            simp [cone] at this
            exact this
          intro x
          simp [Category.comp, c', component]
          congr
          have := h' (Centered.peri x)
          simp [cone] at this
          exact this
        have := h.unique_morphism f'
        change f'.u.val = _
        congr
    use L'
