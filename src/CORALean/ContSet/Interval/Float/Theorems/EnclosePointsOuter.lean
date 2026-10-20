module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.enclosePoints` contains every point

Each coordinate is bounded by `minimumOver` and `maximumOver`, which are under and over every entry.

## Inputs
* `k` – number of points
* `p` – family of float points
* `l` – point index

## Hypotheses
* none

## Conclusion
* point `l` lies in the box enclosing all points
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
