import Ctic.Functor.NatTrans
namespace CTIC

@[ext]
structure Comma [Category C] [Category D] [Category E] (F : D ⥤ C) (G : E ⥤ C) where
  d : D
  e : E
  f : F.obj d ⟶ G.obj e

@[ext]
structure CommaHom [Category C] [Category D] [Category E] {F : D ⥤ C} {G : E ⥤ C} (X Y : Comma F G) where
  k : X.d ⟶ Y.d
  h : X.e ⟶ Y.e
  commu : X.f ≫ G.map h = F.map k ≫ Y.f

instance {C D E : Type*} [Category C] [Category D] [Category E] (F : D ⥤ C) (G : E ⥤ C) : Category (Comma F G) where
  Hom X Y := CommaHom X Y
  id X := by
    apply CommaHom.mk (𝟙 X.d) (𝟙 X.e)
    simp [Functor.map_id]
  comp {X Y Z} := by
    intro f g
    apply CommaHom.mk (f.k ≫ g.k) (f.h ≫ g.h)
    simp [Functor.map_comp]
    rw [f.commu]
    rw [← Category.assoc]
    rw [g.commu]
    rw [Category.assoc]
  assoc {W X Y Z} f g h := by simp [Category.assoc]

def Comma.dom [Category C] [Category D] [Category E] {F : D ⥤ C} {G : E ⥤ C} : Comma F G ⥤ D where
  obj := Comma.d
  map := CommaHom.k

def Comma.cod [Category C] [Category D] [Category E] {F : D ⥤ C} {G : E ⥤ C} : Comma F G ⥤ E where
  obj := Comma.e
  map := CommaHom.h
