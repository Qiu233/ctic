import Ctic.Adjunction
import Ctic.Limit.HasLimits

namespace CTIC

-- class HTensorProduct (α : Type u) (β : Type v) (γ : outParam (Type w)) where
--   hTensor : α → β → γ

-- class TensorProduct (α : Type u) where
--   tensor : α → α → α

-- instance [i : TensorProduct α] : HTensorProduct α α α where
--   hTensor := i.tensor

-- infix:35 " ⊗ " => HTensorProduct.hTensor

abbrev Bifunctor (C D E) [Category C] [Category D] [Category E] := (C × D) ⥤ E

namespace Bifunctor
variable [Category C] [Category D] [Category E]

@[reducible, simp]
def factor_left (F : Bifunctor C D E) (c : C) : D ⥤ E where
  obj X := F (c, X)
  map {X Y} f := F.map ⟨𝟙 c, f⟩
  map_id {X} := by simp [← Functor.map_id]; congr
  map_comp {X Y Z} f g := by simp [← Functor.map_comp]; congr; simp

@[reducible, simp]
def factor_right (F : Bifunctor C D E) (d : D) : C ⥤ E where
  obj X := F (X, d)
  map {X Y} f := F.map ⟨f, 𝟙 d⟩
  map_id {X} := by simp [← Functor.map_id]; congr
  map_comp {X Y Z} f g := by simp [← Functor.map_comp]; congr; simp

end Bifunctor

namespace Functor
variable [Category C] [Category D] [Category E]

@[reducible]
def factor_left (F : (C × D) ⥤ E) : C ⥤ (D ⥤ E) where
  obj c := Bifunctor.factor_left F c
  map {X Y} f := by
    simp [Bifunctor.factor_left]
    use λ d => F.map ⟨f, 𝟙 d⟩
    intro Z W g
    simp
    rw [← Functor.map_comp]
    rw [← Functor.map_comp]
    congr 1
    simp [Category.comp]
  map_id {X} := by
    simp [Bifunctor.factor_left, Category.id, NatTrans.id]
    simp [← Functor.map_id]
    congr
  map_comp {X Y Z} f g := by
    simp [Bifunctor.factor_left, Category.comp, NatTrans.comp]
    simp [← Functor.map_comp]
    congr
    funext t
    congr
    simp

@[reducible]
def factor_right (F : (C × D) ⥤ E) : D ⥤ (C ⥤ E) where --Bifunctor.factor_right F d
  obj d := Bifunctor.factor_right F d
  map {X Y} f := by
    simp [Bifunctor.factor_right]
    use λ c => F.map ⟨𝟙 c, f⟩
    intro Z W g
    simp
    rw [← Functor.map_comp]
    rw [← Functor.map_comp]
    congr 1
    simp [Category.comp]
  map_id {X} := by
    simp [Bifunctor.factor_right, Category.id, NatTrans.id]
    simp [← Functor.map_id]
    congr
  map_comp {X Y Z} f g := by
    simp [Bifunctor.factor_right, Category.comp, NatTrans.comp]
    simp [← Functor.map_comp]
    congr
    funext t
    congr
    simp

example {F G : (C × D) ⥤ E} (η : F ⟹ G) (c : C) : F.factor_left c ⟹ G.factor_left c where
  component X := η (c, X)
  naturality {X Y} f := η.naturality (X := (c, X)) (Y := (c, Y)) ⟨𝟙 c, f⟩

example {F G : (C × D) ⥤ E} (η : F ⟹ G) (d : D) : F.factor_right d ⟹ G.factor_right d where
  component X := η (X, d)
  naturality {X Y} f := η.naturality (X := (X, d)) (Y := (Y, d)) ⟨f, 𝟙 d⟩

example {F G : (C × D) ⥤ E} (η : ∀ (c : C) (d : D), F (c, d) ⟶ G (c, d))
    (α : ∀ c, ∀ d d', ∀ (f : d ⟶ d'), η c d ≫ G.map ⟨𝟙 c, f⟩ = F.map ⟨𝟙 c, f⟩ ≫ η c d')
    (β : ∀ d, ∀ c c', ∀ (f : c ⟶ c'), η c d ≫ G.map ⟨f, 𝟙 d⟩ = F.map ⟨f, 𝟙 d⟩ ≫ η c' d) :
    F ⟹ G where
  component X := η X.fst X.snd
  naturality {X Y} f := by
    simp
    have : f = (⟨𝟙 X.1, f.2⟩ : ((X.1, X.2) ⟶ (X.1, Y.2))) ≫ (⟨f.1, 𝟙 Y.2⟩ : ((X.1, Y.2) ⟶ (Y.1, Y.2))) := by
      simp [Category.comp]
      rfl
    rw [this]
    simp
    rw [α X.1 X.2 Y.2 f.2]
    simp [← Category.assoc]
    congr 1
    rw [β Y.2 X.1 Y.1 f.1]

end Functor

class TensorCategory.{v, u} (C : Type u) extends Category.{v, u} C where
  tensor : (C × C) ⥤ C

notation:310 lhs:310 " ⊗ " rhs:311 => Functor.obj TensorCategory.tensor (lhs, rhs)
notation:310 lhs:310 " ⨂ " rhs:311 => Functor.map TensorCategory.tensor ⟨lhs, rhs⟩

class MonoidalCategory.{v, u} (C : Type u) extends TensorCategory.{v, u} C where
  I : C

  «λ'» (X : C) : I ⊗ X ≅ X
  natural_id_tensor {X Y : C} (f : X ⟶ Y) : («λ'» X).morphism ≫ f = ((𝟙 I) ⨂ f) ≫ («λ'» Y).morphism

  ρ' (X : C) : X ⊗ I ≅ X
  natural_tensor_id {X Y : C} (f : X ⟶ Y) : (ρ' X).morphism ≫ f = (f ⨂ (𝟙 I)) ≫ (ρ' Y).morphism

  α' (X Y Z : C) : X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z
  natural : ∀ {X Y Z X' Y' Z' : C}, ∀ (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    (α' X Y Z).morphism ≫ (f ⨂ g ⨂ h : (X ⊗ Y ⊗ Z ⟶ X' ⊗ Y' ⊗ Z'))
    = f ⨂ (g ⨂ h) ≫ (α' X' Y' Z').morphism

  triangle {X Y : C} :
    (α' X I Y).morphism ≫ ((ρ' X).morphism ⨂ (𝟙 Y) : X ⊗ I ⊗ Y ⟶ X ⊗ Y) =
    (𝟙 X) ⨂ ((«λ'» Y).morphism)

  pentagon {W X Y Z : C} :
    ((𝟙 W) ⨂ (α' X Y Z).morphism) ≫ (α' W (X ⊗ Y) Z).morphism ≫ ((α' W X Y).morphism ⨂ (𝟙 Z)) = (α' W X (Y ⊗ Z)).morphism ≫ (α' (W ⊗ X) Y Z).morphism

@[reducible]
def MonoidalCategory.α [MonoidalCategory.{v, u} C] (X Y Z : C) : X ⊗ (Y ⊗ Z) ⟶ (X ⊗ Y) ⊗ Z := (α' X Y Z).morphism

@[reducible]
def MonoidalCategory.«λ» [MonoidalCategory.{v, u} C] (X : C) : I ⊗ X ⟶ X := («λ'» X).morphism

@[reducible]
def MonoidalCategory.ρ [MonoidalCategory.{v, u} C] (X : C) : X ⊗ I ⟶ X := (ρ' X).morphism

open Lean PrettyPrinter Delaborator SubExpr Meta in
section

@[delab app.CTIC.Isomorphism.morphism]
def delab_Isomorphism_morphism_MonoidalCategory : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 5
  withNaryArg 4 do α <|> id_tensor <|> tensor_id
where
  α := do
    let e ← getExpr
    guard <| e.isAppOfArity ``CTIC.MonoidalCategory.α' 5
    let fn := e.getAppFn
    let (_, ls) ← fn.const?.getM
    let t := e.updateFn (Expr.const ``CTIC.MonoidalCategory.α ls)
    withTheReader SubExpr (fun cfg => { cfg with expr := t }) delab
  id_tensor := do
    let e ← getExpr
    guard <| e.isAppOfArity ``CTIC.MonoidalCategory.«λ'» 3
    let fn := e.getAppFn
    let (_, ls) ← fn.const?.getM
    let t := e.updateFn (Expr.const ``CTIC.MonoidalCategory.«λ» ls)
    withTheReader SubExpr (fun cfg => { cfg with expr := t }) delab
  tensor_id := do
    let e ← getExpr
    guard <| e.isAppOfArity ``CTIC.MonoidalCategory.ρ' 3
    let fn := e.getAppFn
    let (_, ls) ← fn.const?.getM
    let t := e.updateFn (Expr.const ``CTIC.MonoidalCategory.ρ ls)
    withTheReader SubExpr (fun cfg => { cfg with expr := t }) delab

end

class CartesianCategory.{v, u} (C : Type u) extends MonoidalCategory.{v, u} C where
  cartesian (X Y : C) : Contravariant.RepresentedBy Hom[Δ(-), Diagram.Binary.Discrete.{v, u} X Y] (X ⊗ Y)

@[reducible]
def Prod.bifunctor : (Type u × Type u) ⥤ Type u where
  obj X := X.1 × X.2
  map {X Y} f x := ⟨f.1 x.1, f.2 x.2⟩

notation:500 "[" X:500 " ⊗ " "-" "]" => TensorCategory.tensor.factor_left X
notation:500 "[" "-" " ⊗ " Y:500 "]" => TensorCategory.tensor.factor_right Y

class MonoidalClosed.{v, u} (C : Type u) extends MonoidalCategory.{v, u} C where
  exp : (Cᵒᵖ × C) ⥤ C
  adj (X : C) : [-⊗X] ⊣ exp.factor_left Xᵒᵖ

class CartesianClosed.{v, u} (C : Type u) extends MonoidalClosed.{v, u} C, CartesianCategory.{v, u} C where

instance [inst : MonoidalClosed C] : HomogeneousPow C where
  pow X Y := inst.exp (Xᵒᵖ, Y)

notation:500 "[" X:500 ", " "-" "]" => MonoidalClosed.exp.factor_left Xᵒᵖ
notation:500 "[" "-" ", " Y:500 "]" => MonoidalClosed.exp.factor_right  Y

open Lean PrettyPrinter Delaborator SubExpr Meta in
section

@[delab app.CTIC.Functor.obj]
private def delab_Functor_obj_tensor : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  let inop? ← ((e.getArg! 5).app4? ``HasOpposite.op).mapM fun (_, _, _, _) => withNaryArg 5 do withNaryArg 3 do delab
  let expr ← withNaryArg 5 delab
  let e := e.getArg! 4
  if e.isAppOfArity ``Functor.factor_left 7 then
    if (e.getArg! 6).isAppOfArity ``TensorCategory.tensor 2 then
      `([$expr ⊗ -])
    else if (e.getArg! 6).isAppOfArity ``MonoidalClosed.exp 2 then
      match inop? with
      | none => `([$exprᵒᵖ, -])
      | some inop => `([$inop, -])
    else failure
  else if e.isAppOfArity ``Functor.factor_right 7 then
    if (e.getArg! 6).isAppOfArity ``TensorCategory.tensor 2 then
      `([- ⊗ $expr])
    else if (e.getArg! 6).isAppOfArity ``MonoidalClosed.exp 2 then
      `([-, $expr])
    else failure
  else failure

end

open Lean in
@[app_unexpander Functor.obj]
private def unexpand_exp : PrettyPrinter.Unexpander
  | `($(_) $f $yᵒᵖ) =>
    match f with
    | `([-, $x]) => `($y ^ $x)
    | _ => throw ()
  | `($(_) $f $y) =>
    match f with
    | `([$x, -]) => `($x ^ $y)
    | `([-, $x]) => `($yᵒᵖ ^ $x)
    | _ => throw ()
  | _ => throw ()

variable [MonoidalClosed C] in
section

@[simp]
private theorem reduce_exp_fl {X Y : C} : [X, -].obj Y = X ^ Y := by rfl

@[simp]
private theorem reduce_exp_fr {X Y : C} : [-, Y].obj Xᵒᵖ = X ^ Y := by rfl

@[simp]
private theorem reduce_exp_fr' {X : Cᵒᵖ} {Y : C} : [-, Y].obj X = Xᵒᵖ ^ Y := by rfl

end

namespace Prod

instance : TensorCategory (Type u) where
  tensor := Prod.bifunctor

@[reducible]
def id_tensor (X : Type u) : (PUnit × X) ≅ X where
  morphism := Prod.snd
  inverse := Prod.mk PUnit.unit
  forward := by rfl
  backward := by rfl

@[reducible]
def tensor_id (X : Type u) : (X × PUnit) ≅ X where
  morphism := Prod.fst
  inverse := (Prod.mk · PUnit.unit)
  forward := by rfl
  backward := by rfl

@[reducible]
def tensor_assoc (X Y Z) : (X × (Y × Z)) ≅ ((X × Y) × Z) where
  morphism := λ (x, y, z) ↦ ((x, y), z)
  inverse := λ ((x, y), z) ↦ (x, y, z)
  forward := by rfl
  backward := by rfl

instance : MonoidalCategory (Type u) where
  I := PUnit
  «λ'» := id_tensor
  ρ' := tensor_id
  α' := tensor_assoc
  natural_id_tensor {X Y} f := by rfl
  natural_tensor_id {X Y} f := by rfl
  natural {X Y Z X' Y' Z'} f g h := by rfl
  triangle {X Y} := by rfl
  pentagon {W X Y Z} := by rfl

def exp_functor : ((Type u)ᵒᵖ × Type u) ⥤ Type u where
  obj := λ ⟨X, Y⟩ => Xᵒᵖ → Y
  map {L R} f := by
    obtain ⟨⟨X⟩, Y⟩ := L
    obtain ⟨⟨A⟩, B⟩ := R
    obtain ⟨f : A ⟶ X, g : Y ⟶ B⟩ := f
    exact (f ≫ · ≫ g)

def tensor_hom (X : Type u) : Prod.bifunctor.factor_right X ⊣ exp_functor.factor_left (Opposite.op X) where
  η := ⟨fun A a x => ⟨a, x⟩, by intros; funext; rfl⟩
  ε := ⟨fun A (f, x) => f x, by intros; funext; rfl⟩
  upper := by intro _; rfl
  lower := by intro _; rfl

instance : CartesianClosed (Type u) where
  exp := exp_functor
  adj := tensor_hom
  cartesian {X Y} := by
    refine Contravariant.RepresentedBy.intro ?_
    let s : Δ (X ⊗ Y) ⟶ Diagram.Binary.Discrete X Y := by
      use fun
        | 0 => Prod.fst
        | 1 => Prod.snd
      intro a b f
      cases f.down
      match a with
      | 0 | 1 => rfl
    let p := Yoneda.Contravariant.t2 Hom[Δ(-), Diagram.Binary.Discrete X Y] (X ⊗ Y) ⟨s⟩
    let q : Hom[Δ(-), Diagram.Binary.Discrete X Y] ⟹ HomCon (X ⊗ Y) := by
      use fun ⟨P⟩ f p => ⟨f.component 0 p, f.component 1 p⟩
      intros
      rfl
    use p, q
    . rfl
    . simp [Category.id, Category.comp, NatTrans.id, NatTrans.comp]
      congr
      funext ⟨P⟩ f
      rw [NatTrans.ext_iff]
      funext t
      match t with
      | 0 | 1 => rfl

end Prod

example [CartesianCategory.{v, u} C] : HasLimitsOfShape C (Discrete (Fin 2)) where
  limits F := by
    apply HasLimit.intro
    -- constructor
