import Ctic.Repre.Yoneda

namespace CTIC.Contravariant

open Yoneda.Notation

@[ext]
structure Representation.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) where
  obj : C
  iso : Hom[-, obj] ≅ F

class inductive Representable.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) : Prop where
  | intro (rep : Representation F)

inductive RepresentedBy.{v, u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) (c : C) : Type max v u where
  | intro (iso : Hom[-, c] ≅ F)

protected abbrev CategoryOfElements.{v, u} {C : Type u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v) : Type max u v := Comma (Yoneda.Contravariant.Embedding (C := C)) (TrivialFunctor F)

scoped prefix:max "∫ " => Contravariant.CategoryOfElements

universe v u

variable {C : Type u} [Category.{v, u} C] {F : Cᵒᵖ ⥤ Type v}

lemma isic_of_terminal_in_category_of_elements
    [decEq : ∀ X, DecidableEq (F X)] {L : ∫ F} (terminal : Terminal L) : Invertible L.f := by
  obtain ⟨c, u, α⟩ := L
  change Hom[-, c] ⟶ F at α
  apply NatTrans.isic_of_components_isic
  intro X
  simp
  apply Invertible.of_monic_and_epic_of_sets
  . rw [Function.Monic_iff_Injective]
    intro f g h1
    change Xᵒᵖ ⟶ c at f g
    let s : ∫ F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.t2 F Xᵒᵖ ⟨(α.component X) f⟩⟩
    let t : ∫ F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.t2 F Xᵒᵖ ⟨(α.component X) g⟩⟩
    let p := terminal.morphism s
    let q := terminal.morphism t
    have h2 : s = t := by simp [s, t]; rw [h1]
    have h3 : p.k = q.k := by
      simp [p, q]
      congr
    have h5 : ((Yoneda.Contravariant.Embedding (C := C)).map f ≫ α) = Yoneda.Contravariant.t2 F Xᵒᵖ ⟨α.component X f⟩ := by
      have := Yoneda.Contravariant.monic_t1 F Xᵒᵖ
      rw [Function.Monic_iff_Injective] at this
      apply this
      rw [← Function.comp_apply (f := Yoneda.Contravariant.t1 F Xᵒᵖ)]
      rw [← Function.comp_apply (f := Yoneda.Contravariant.t1 F Xᵒᵖ)]
      have : (Yoneda.Contravariant.t1 F Xᵒᵖ) ∘ (Yoneda.Contravariant.t2 F Xᵒᵖ) = 𝟙 (ULift (F X)) := by
        funext ⟨t⟩
        dsimp [Yoneda.Contravariant.t1, Yoneda.Contravariant.t2]
        congr
        change F.map (𝟙 X) t = (𝟙 F X) t
        rw [Functor.map_id]
      rw [this]
      simp [Category.id, Yoneda.Contravariant.iso, Yoneda.Contravariant.Embedding, Yoneda.Contravariant.t1, Category.comp]
    have h6 := p.commu
    change s.f = (Yoneda.Contravariant.Embedding (C := C)).map p.k ≫ α at h6
    have h7 := terminal.unique (X := s) (f := ⟨f, (), h5.symm⟩)
    have h8 : f = p.k := by
      rw [CommaHom.ext_iff] at h7
      simp at h7
      simp [h7]
    have h10 : ((Yoneda.Contravariant.Embedding (C := C)).map g ≫ α) = (Yoneda.Contravariant.t2 F Xᵒᵖ) ⟨α.component X g⟩ := by
      have := (Yoneda.Contravariant.monic_t1 F Xᵒᵖ)
      rw [Function.Monic_iff_Injective] at this
      apply this
      rw [← Function.comp_apply (f := Yoneda.Contravariant.t1 F Xᵒᵖ)]
      rw [← Function.comp_apply (f := Yoneda.Contravariant.t1 F Xᵒᵖ)]
      have : (Yoneda.Contravariant.t1 F Xᵒᵖ) ∘ (Yoneda.Contravariant.t2 F Xᵒᵖ) = 𝟙 (ULift (F X)) := by
        funext ⟨t⟩
        dsimp [Yoneda.Contravariant.t1, Yoneda.Contravariant.t2]
        congr
        change F.map (𝟙 X) t = (𝟙 F X) t
        rw [Functor.map_id]
      rw [this]
      simp [Category.id, Yoneda.Contravariant.iso, Yoneda.Contravariant.Embedding, Yoneda.Contravariant.t1, Category.comp]
    have h11 := q.commu
    change t.f = (Yoneda.Contravariant.Embedding (C := C)).map q.k ≫ α at h11
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
    let s : ∫ F := ⟨Xᵒᵖ, (), Yoneda.Contravariant.t2 F Xᵒᵖ ⟨e⟩⟩
    have h1 : s.f.component X (𝟙 X) = e := by
      simp [s, Yoneda.Contravariant.iso]
      change (F.map (𝟙 X)) e = e
      rw [Functor.map_id (X := X)]
      simp [Category.id]
    let t := terminal.morphism s
    have h2 := t.commu
    change s.f = (Yoneda.Contravariant.Embedding (C := C)).map t.k ≫ α at h2
    have h3 : (α.component X) t.k = s.f.component X (𝟙 X) := by
      rw [h2]
      simp [Yoneda.Contravariant.Embedding]
      simp [Category.comp]
      rw [Category.id_comp (x := X.unop) (f := t.k)]
    have h4 := Eq.trans h3 h1
    use t.k

noncomputable
def terminal_in_category_of_elements_of_isic.morphism {L : ∫ F} (isic : Invertible L.f) : (X : ∫ F) → X ⟶ L := by
  intro X
  let t : Hom[-, X.d] ⟶ Hom[-, L.d] := X.f ≫ isic.choose
  use (Yoneda.Contravariant.FullyFaithful (C := C)).inv t, ()
  simp [t]
  have := isic.choose_spec
  rw [← Category.assoc]
  rw [this.2]
  simp

lemma terminal_in_category_of_elements_of_isic.unique {L : ∫ F} (isic : Invertible L.f) :
    ∀ (X : ∫ F) (f : X ⟶ L), f = terminal_in_category_of_elements_of_isic.morphism isic X := by
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

lemma terminal_in_category_of_elements_of_isic {L : ∫ F} (isic : Invertible L.f) : Nonempty (Terminal L) :=
  Nonempty.intro ⟨terminal_in_category_of_elements_of_isic.morphism isic,
    fun {X f} => terminal_in_category_of_elements_of_isic.unique isic X f⟩

theorem isic_iff_terminal_in_category_of_elements
    [decEq : ∀ X, DecidableEq (F X)] (L : ∫ F) : Nonempty (Terminal L) ↔ Invertible L.f :=
  ⟨fun ⟨ne⟩ => isic_of_terminal_in_category_of_elements ne, terminal_in_category_of_elements_of_isic⟩

theorem isic_iff_exists_terminal_in_category_of_elements
    {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type v) [decEq : ∀ X, DecidableEq (F X)] : Representable F ↔ ∃ (L : ∫ F), Nonempty (Terminal L) := by
  apply Iff.intro
  . intro ⟨⟨c, α⟩⟩
    let t : ∫ F := ⟨c, (), α.morphism⟩
    use t
    exact terminal_in_category_of_elements_of_isic (α.invertible)
  . intro ⟨L, ⟨terminal⟩⟩
    have i := isic_of_terminal_in_category_of_elements terminal
    apply Representable.intro
    apply Representation.mk L.d (Isomorphism.of_invertible i)

noncomputable
def Representation.cong
    [decEq : ∀ X, DecidableEq (F X)] :
    Representation F ≅ Σ' (L : ∫ F), Terminal L := by
  let f : Representation F → (L : ∫ F) ×' Terminal L := by
    intro r
    let t : ∫ F := ⟨r.obj, (), r.iso.morphism⟩
    use t
    use terminal_in_category_of_elements_of_isic.morphism r.iso.invertible
    intro X f
    have := terminal_in_category_of_elements_of_isic.unique (F := F) ((show t.f = r.iso.morphism by rfl) ▸ r.iso.invertible)
    apply this
  let g : (L : ∫ F) ×' Terminal L → Representation F := by
    intro ⟨L, terminal⟩
    have i := isic_of_terminal_in_category_of_elements terminal
    apply Representation.mk L.d (Isomorphism.of_invertible i)
  use f, g
  . simp [f, g]
    simp [Category.id, Category.comp]
    funext r
    simp
    rw [Representation.ext_iff]
    simp [Isomorphism.of_invertible]
    rw [Isomorphism.ext_iff]
  . simp [f, g]
    simp [Category.id, Category.comp]
    funext ⟨L, terminal⟩
    simp
    apply And.intro
    . rw [Comma.ext_iff]
      simp
      simp [Isomorphism.of_invertible]
    . congr
      unfold terminal_in_category_of_elements_of_isic.morphism
      funext X
      simp
      apply terminal.unique (X := X)

@[simp]
theorem Representation.cong_map
    [decEq : ∀ X, DecidableEq (F X)] (r : Representation F) :
    (Representation.cong.morphism r).fst.d = r.obj := by rfl

@[simp]
theorem Representation.cong_inv
    [decEq : ∀ X, DecidableEq (F X)] (L : Σ' (L : ∫ F), Terminal L) :
    (Representation.cong.inverse L).obj = L.fst.d := by rfl

@[simp]
theorem Representation.cong_inv'
    [decEq : ∀ X, DecidableEq (F X)] (L : ∫ F) (terminal : Terminal L) :
    (Representation.cong.inverse ⟨L, terminal⟩).obj = L.d := by rfl

theorem nat_trans_eq_iff_component_eq {C : Type u} {D : Type u1} [Category.{v} C] [Category D] {c : C}
    {F : Cᵒᵖ ⥤ Type v} (α β : Hom[-, c] ⟶ F) : α = β ↔ (α.component cᵒᵖ (𝟙 c)) = (β.component cᵒᵖ (𝟙 c)) := by
  apply Iff.intro
  . intro h
    have : (Yoneda.Contravariant.iso F c).morphism α = (Yoneda.Contravariant.iso F c).morphism β := by rw [h]
    simp [Yoneda.Contravariant.iso, Yoneda.Contravariant.t1] at this
    rw [ULift.ext_iff] at this
    exact this
  . intro h
    have := (Yoneda.Contravariant.iso F c).monic
    rw [Function.Monic_iff_Injective] at this
    apply this
    simp [Yoneda.Contravariant.iso, Yoneda.Contravariant.t1]
    rw [h]

private def rep2terminal [Category C] [Category D] {d : D} (F : C ⥤ D) : Representation Hom[F(-), d] → Σ' (c : Comma F (TrivialFunctor d)), Terminal c := by
  intro ⟨c, α⟩
  let c' : Comma F (TrivialFunctor d) := ⟨c, (), α.morphism.component cᵒᵖ (𝟙 c)⟩
  use c'
  let m : (X : Comma F (TrivialFunctor d)) → X ⟶ c' := by
    intro X
    let g := α.inverse.component X.dᵒᵖ X.f
    use g, ()
    simp
    have := α.morphism.naturality g
    rw [funext_iff] at this
    specialize this (𝟙 c)
    change (α.morphism.component cᵒᵖ ≫ Hom[F(-), d].map g) (𝟙 c) = (α.morphism.component X.dᵒᵖ) (g ≫ 𝟙 c) at this
    rw [Category.comp_id] at this
    change F.map g ≫ (α.morphism.component cᵒᵖ (𝟙 c)) = (α.morphism.component X.dᵒᵖ) g at this
    rw [this]
    let elem : ∫ Hom[F(-), d] := ⟨c, (), α.morphism⟩
    have ⟨terminal⟩ := Contravariant.terminal_in_category_of_elements_of_isic (L := elem) α.invertible
    let X' : ∫ Hom[F(-), d] := ⟨X.d, (), Yoneda.Contravariant.iso Hom[F(-), d] X.d |>.inverse ⟨X.f⟩⟩
    let s : X' ⟶ elem := ⟨g, (), by
        have := (Yoneda.Contravariant.iso Hom[F(-), d] X.d).monic
        rw [Function.Monic_iff_Injective] at this
        apply this
        rw [← Function.comp_apply (f := (Yoneda.Contravariant.iso Hom[F(-), d] X.d).morphism)]
        change ((Yoneda.Contravariant.iso Hom[F(-), d] X.d).inverse ≫ (Yoneda.Contravariant.iso Hom[F(-), d] X.d).morphism)
              { down := X.f } =
            (Yoneda.Contravariant.iso Hom[F(-), d] X.d).morphism (Yoneda.Contravariant.Embedding.map g ≫ α.morphism)
        rw [(Yoneda.Contravariant.iso Hom[F(-), d] X.d).backward]
        change { down := X.f : ULift (Hom[F X.d, d]) } = { down := (Yoneda.Contravariant.Embedding.map g ≫ α.morphism).component X.dᵒᵖ (𝟙 X.d) }
        rw [ULift.ext_iff]
        change X.f = α.morphism.component X.dᵒᵖ (𝟙 X.d ≫ g)
        rw [Category.id_comp (x := X.d) (f := g)]
        change X.f = ((α.inverse.component X.dᵒᵖ) ≫ (α.morphism.component X.dᵒᵖ)) X.f
        rw [α.backward_iso]
        rfl
      ⟩
    have eq := terminal.unique (f := s)
    have := terminal.morphism X' |>.commu
    simp [Yoneda.Contravariant.iso, Yoneda.Contravariant.t2, Yoneda.Contravariant.Embedding] at this
    change X'.f = Yoneda.Contravariant.Embedding.map (Terminal.morphism X').k ≫ elem.f at this
    have := eq ▸ this
    change X'.f = Yoneda.Contravariant.Embedding.map g ≫ α.morphism at this
    change (Yoneda.Contravariant.iso Hom[F(-), d] X.d |>.inverse ⟨X.f⟩) = Yoneda.Contravariant.Embedding.map g ≫ α.morphism at this
    simp [Yoneda.Contravariant.iso, Yoneda.Contravariant.t2, Yoneda.Contravariant.Embedding] at this
    simp [Category.comp] at this
    have := funext_iff.mp this X.dᵒᵖ
    have := funext_iff.mp this (𝟙 X.d)
    simp at this
    change Hom[F(-), d].map (𝟙 X.dᵒᵖ) X.f = (α.morphism.component X.dᵒᵖ) g at this
    simp [Yoneda.Contravariant.Embedding, HomCon, Functor.comp] at this
    change ((𝟙 (F X.d)) ≫ X.f) = (α.morphism.component X.dᵒᵖ) g at this
    rewrite [Category.id_comp (x := F X.d)] at this
    exact this
  use m
  intro X ⟨g, h, commu⟩
  change Hom[X.d, c'.d] at g
  change X.f ≫ 𝟙 d = F.map g ≫ c'.f at commu
  rw [Category.comp_id (y := d)] at commu
  rw [CommaHom.ext_iff]
  simp
  refine ⟨?_, by rfl⟩
  clear h
  have : Monic (α.morphism.component X.dᵒᵖ) := (α.component X.dᵒᵖ).monic
  rw [Function.Monic_iff_Injective] at this
  apply this
  change (α.morphism.component X.dᵒᵖ) g = (α.inverse.component X.dᵒᵖ ≫ α.morphism.component X.dᵒᵖ) X.f
  simp
  change (α.morphism.component X.dᵒᵖ) g = X.f
  rw [commu]
  have := α.morphism.naturality g
  simp at this
  rw [funext_iff] at this
  specialize this (𝟙 c)
  simp [Category.comp] at this
  rw [← this]
  rfl

private def terminal2rep [Category C] [Category D] {d : D} (F : C ⥤ D) : (Σ' (c : Comma F (TrivialFunctor d)), Terminal c) → Representation Hom[F(-), d] := by
  intro ⟨c, terminal⟩
  use c.d
  let m := Yoneda.Contravariant.t2 Hom[F(-), d] c.d ⟨c.f⟩
  let n : Hom[F(-), d] ⟹ Hom[-, c.d] := by
    use fun ⟨x⟩ t => (terminal.morphism ⟨x, (), t⟩).k
    intro ⟨X⟩ ⟨Y⟩ (f : Y ⟶ X)
    funext (t : F X ⟶ d)
    simp [Category.comp]
    let p : Comma F (TrivialFunctor d) := ⟨X, (), t⟩
    let q : Comma F (TrivialFunctor d) := ⟨Y, (), Hom[F(-), d].map f t⟩
    change f ≫ (terminal.morphism p).k = (terminal.morphism q).k
    let s : CommaHom q c := ⟨f ≫ (Terminal.morphism p).k, (), by
      simp [Yoneda.Contravariant.Embedding, HomCon, Functor.comp]
      have := (terminal.morphism q).commu
      have := (terminal.morphism p).commu
      simp at this
      rw [← Category.assoc]
      rw [← this]
      ⟩
    have := terminal.unique (f := s)
    rw [← this]
  use m, n
  . rw [NatTrans.ext_iff]
    funext ⟨x⟩
    simp [m, n, Yoneda.Contravariant.t2, Yoneda.Contravariant.Embedding, HomCon]
    simp [Category.comp, Functor.comp, Category.id]
    funext t
    simp
    let p : Comma F (TrivialFunctor d) := ⟨x, (), F.map t ≫ c.f⟩
    change (terminal.morphism p).k = t
    let s : CommaHom p c := ⟨t, (), by simp⟩
    have := terminal.unique (f := s)
    rw [← this]
  . rw [NatTrans.ext_iff]
    funext ⟨x⟩
    simp [m, n, Yoneda.Contravariant.t2, Yoneda.Contravariant.Embedding, HomCon]
    simp [Category.comp, Functor.comp, Category.id]
    funext (t : F x ⟶ d)
    simp
    let p : Comma F (TrivialFunctor d) := ⟨x, (), t⟩
    change F.map (terminal.morphism p).k ≫ c.f = t
    have := (terminal.morphism p).commu
    simp at this
    rw [this]

def down [Category C] [Category D] {d : D} (F : C ⥤ D) : Representation Hom[F(-), d] ≅ Σ' (c : Comma F (TrivialFunctor d)), Terminal c := by
  use rep2terminal F, terminal2rep F
  . unfold CTIC.Contravariant.rep2terminal CTIC.Contravariant.terminal2rep
    simp [Category.comp, Category.id]
    funext ⟨c, α⟩
    simp
    apply Isomorphism.ext
    simp [Yoneda.Contravariant.t2, Functor.comp]
    rw [NatTrans.ext_iff]
    simp
    funext ⟨t⟩
    funext (f : t ⟶ c)
    have := α.morphism.naturality f
    simp [Yoneda.Contravariant.Embedding, HomCon, Category.comp, Functor.comp] at this
    rw [funext_iff] at this
    specialize this (𝟙 c)
    simp at this
    exact this
  . unfold CTIC.Contravariant.rep2terminal CTIC.Contravariant.terminal2rep
    simp [Category.comp, Category.id]
    funext ⟨c, α⟩
    simp
    apply And.intro
    . simp [Yoneda.Contravariant.Embedding, HomCon, Category.comp, Functor.comp]
      rw [Category.id_comp (x := F c.d)]
    . have : { d := c.d, e := (), f := (Fᵒᵖ ⋙ Hom[-, d]).map (𝟙 c.dᵒᵖ) c.f } = c := by
        rw [Comma.ext_iff]
        simp
        simp [Yoneda.Contravariant.Embedding, HomCon, Category.comp, Functor.comp]
        rw [Category.id_comp (x := F c.d)]
      apply HEq.trans (b := this ▸ α)
      . congr
        funext x
        rw [CommaHom.ext_iff]
        simp
        apply And.intro
        . have : { d := x.d, e := (), f := x.f } = x := by rfl
          congr
          . simp [Yoneda.Contravariant.Embedding, HomCon, Category.comp, Functor.comp]
            rw [Category.id_comp (x := F c.d)]
          . simp [Yoneda.Contravariant.Embedding, HomCon, Category.comp, Functor.comp]
            rw [Category.id_comp (x := F c.d)]
          . simp
        . rfl
      . apply eq_rec_heq

-- example [Category C] [Category D] {d : D} (F : C ⥤ D) : ∀ (r : Representation Hom[F(-), d]), ((down F).morphism r).fst.d = r.obj := by intro; rfl
