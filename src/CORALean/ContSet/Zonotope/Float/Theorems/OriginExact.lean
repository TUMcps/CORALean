import CORALean.ContSet.Zonotope.Float.Operations.Origin
import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

/-!
# `Zonotope.origin` is exactly the origin

`zero` reads as `0`, so the stored centre is the exact layer's origin and the
point theorem gives `{0}`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.origin_exact (n : ℕ) :
    (Zonotope.origin n : Zonotope (Vec 𝕋 n)).construct = {0} := by
  have h : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  rw [Zonotope.origin, Zonotope.construct_point, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
