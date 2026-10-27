module

public import CORALean.ContSet.Interval.Float.Theorems.VecExact
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaOriginSound

@[expose] public section

/-!
# `Interval.vec` decides whether an interval matrix is the zero matrix

CORA's `representsa(intMat, 'origin')` stacks the bounds and tests the stacked interval. A `true`
from the float test on the stacked bounds says the stacked set is the origin, and stacking is a
bijection, so the matrix set is the zero matrix.

## Inputs
* `I` – interval matrix

## Hypotheses
* `h` – the float test on the stacked bounds is `true`

## Conclusion
* the interval matrix denotes exactly the zero matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vec_representsa_origin_sound {I : Interval (Mat 𝕋 m n)}
    (h : I.vec.representsa_origin = true) :
    I.construct = {0} := by
  have h1 := Interval.representsa_origin_sound h
  rw [Interval.vec_exact, ← map_zero matVecEquiv, ← Set.image_singleton] at h1
  exact matVecEquiv.injective.image_injective h1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
