import CORALean.ContSet.Interval.Float.Operations.EnclosePoints

/-!
# `Interval.enclosePoints` contains every point

Each coordinate is bounded by `minimumOver` and `maximumOver`, which are under and over every entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.enclosePoints_outer {k : ℕ} (p : Fin k → Vec 𝕋 n) (l : Fin k) :
    toRealVec (p l) ∈ (Interval.enclosePoints p).construct := fun i =>
  ⟨minimumOver_le (fun l => p l i) l, le_maximumOver (fun l => p l i) l⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
