import Ctic.Functor.Equiv
namespace CTIC

def Isomorphism.map_iso [Category C] [Category D] {F G : C ⥤ D} (iso : F ≅ G) (X Y : C) : (F.obj X ⟶ F.obj Y) ≅ (G.obj X ⟶ G.obj Y) where
  morphism f := iso.inverse.component X ≫ f ≫ iso.morphism.component Y
  inverse f := iso.morphism.component X ≫ f ≫ iso.inverse.component Y
  forward := by
    funext f
    simp [Category.comp, Category.id]
    simp [← Category.assoc]
  backward := by
    funext f
    simp [Category.comp, Category.id]
    simp [← Category.assoc]

@[simp]
theorem Isomorphism.map_iso_def [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X Y : C} {f : F.obj X ⟶ F.obj Y} : (iso.map_iso X Y).morphism f = iso.inverse.component X ≫ f ≫ iso.morphism.component Y := by
  simp [Isomorphism.map_iso]

@[simp]
theorem Isomorphism.map_iso_inv [Category C] [Category D] {F G : C ⥤ D} {iso : F ≅ G} {X Y : C} {f : G.obj X ⟶ G.obj Y} : (iso.map_iso X Y).inverse f = iso.morphism.component X ≫ f ≫ iso.inverse.component Y := by
  simp [Isomorphism.map_iso]

def Isomorphism.trans_essentially_surjective [Category C] [Category D] {F G : C ⥤ D} : F ≅ G → F.EssentiallySurjective → G.EssentiallySurjective := by
  intro iso es d
  let ⟨c, hc⟩ := es d
  let t := iso.component c |>.symm
  use c
  apply t.comp hc

def Isomorphism.trans_essentially_injective [Category C] [Category D] {F G : C ⥤ D} : F ≅ G → F.EssentiallyInjective → G.EssentiallyInjective := by
  intro iso ei X Y h
  let f' := ((iso.component X).comp h).comp (iso.component Y).symm
  apply ei X Y f'

theorem Isomorphism.trans_full [Category C] [Category D] {F G : C ⥤ D} : F ≅ G → F.Full → G.Full := by
  intro iso full X Y g'
  let f' := iso.morphism.component X ≫ g' ≫ iso.inverse.component Y
  have ⟨f, hf⟩ := full (X := X) (Y := Y) f'
  use f
  simp [f'] at hf
  apply iso.component_epic
  apply iso.component_inv_monic
  simp [← hf, iso.morphism.naturality, ← Category.assoc]

theorem Isomorphism.trans_faithful [Category C] [Category D] {F G : C ⥤ D} : F ≅ G → F.Faithful → G.Faithful := by
  intro iso faithful X Y f1 f2 h1
  apply faithful
  apply iso.component_monic
  rw [← iso.morphism.naturality]
  apply iso.component_inv_epic
  simp [h1]
  apply iso.component_inv_monic
  simp [← Category.assoc]
  rw [iso.inverse.naturality]
