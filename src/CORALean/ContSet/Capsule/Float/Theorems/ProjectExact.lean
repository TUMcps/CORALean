import CORALean.ContSet.Capsule.Float.Operations.Project
import CORALean.ContSet.Capsule.Real.Theorems.ProjectExact

/-!
# `Capsule.project` is exactly the projected set, over a floating-point scalar

Reading the stored floats commutes with selecting coordinates, so the nominal capsule of the
projection is the exact layer's projection of the nominal capsule.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.project_exact (C : Capsule 𝕋 n) {dims : Fin m → Fin n}
    (hd : Function.Injective dims) :
    (C.project dims).construct =
      (fun x : Vec ℝ n => fun i => x (dims i)) '' C.construct :=
  Real.Capsule.project_exact C.nominal hd

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
