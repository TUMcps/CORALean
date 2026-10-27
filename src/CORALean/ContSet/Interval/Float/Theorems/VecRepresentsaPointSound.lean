module

public import CORALean.ContSet.Interval.Float.Theorems.VecExact
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# `Interval.vec` decides whether an interval matrix is a single matrix

CORA's `representsa(intMat, 'point')` stacks the bounds and tests the stacked interval. A `true`
from the float test on the stacked bounds says the stacked set is one vector, and stacking is a
bijection, so the matrix set is one matrix.

## Inputs
* `I` – interval matrix

## Hypotheses
* `h` – the float test on the stacked bounds is `true`

## Conclusion
* the interval matrix denotes a single matrix
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

theorem Interval.vec_representsa_point_sound {I : Interval (Mat 𝕋 m n)}
    (h : I.vec.representsa_point = true) :
    ∃ A, I.construct = {A} := by
  obtain ⟨v, hv⟩ := Interval.representsa_point_sound h
  refine ⟨matVecEquiv.symm v, ?_⟩
  rw [Interval.vec_exact, ← matVecEquiv.apply_symm_apply v, ← Set.image_singleton] at hv
  exact matVecEquiv.injective.image_injective hv

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
