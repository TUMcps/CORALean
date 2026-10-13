import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes

/-!
# `mtimes` does not touch the constraint system

The stored system and the factors it ranges over are the same before and
after the map, so satisfaction transfers by `Iff.rfl`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constraint says of the image what it said of the argument, the stored
system being the same floats over the same factors. -/
theorem ConPolyZono.satisfies_mtimes (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin cPZ.p → ℝ) : (ConPolyZono.mtimes M cPZ).satisfies a ↔ cPZ.satisfies a := Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
