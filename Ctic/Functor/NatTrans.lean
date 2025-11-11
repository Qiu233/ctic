import Ctic.Functor.NatTrans.Basic
import Ctic.Functor.NatTrans.Component

namespace CTIC

@[simp]
theorem Functor.id_functor_app [Category C] [Category D] (F : C ⥤ D) (x : C) : (𝟙 F).component x = 𝟙 (F x) := by rfl
