import Ctic.Category
import Ctic.Functor

namespace CTIC

def Discrete (α : Type u) := α

instance : Category (Discrete α) where
  Hom X Y := PLift (X = Y)
  id X := ⟨by simp⟩
  comp f g := ⟨Eq.trans f.down g.down⟩
  assoc := by simp

namespace Diagram

scoped notation:max "𝟬" => Discrete (Fin 0)
scoped notation:max "𝟐" => Discrete (Fin 2)

@[simp]
private abbrev Binary.Discrete.obj [Category C] (X Y : C) : 𝟐 → C := fun (c : Fin 2) =>
  match c with
  | 0 => X
  | 1 => Y

@[simp]
private abbrev Binary.Discrete.map [Category C] (X Y : C) {A B : 𝟐} :
    (A ⟶ B) → (Diagram.Binary.Discrete.obj X Y A ⟶ Diagram.Binary.Discrete.obj X Y B) := fun f => by
  change Fin 2 at A B
  simp [Diagram.Binary.Discrete.obj]
  cases f.down
  match A with
  | 0 => exact 𝟙 X
  | 1 => exact 𝟙 Y

@[reducible]
def Binary.Discrete.{v, u} [inst : Category.{v, u} C] (X Y : C) : 𝟐 ⥤ C where
  obj := Diagram.Binary.Discrete.obj X Y
  map := Diagram.Binary.Discrete.map X Y
  map_id {A} := by
    change Fin 2 at A
    match A with
    | 0 => rfl
    | 1 => rfl
  map_comp {A B C} f g := by cases f.down; cases g.down; change Fin 2 at A; match A with | 0 | 1 => simp

theorem Nullary.empty (x : 𝟬) : False := by
  have ⟨x, h⟩ := x
  apply Nat.not_lt_zero _ h
