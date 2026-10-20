module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpW
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpWFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HalfSqBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# The float `expW` holds the exact one

`W(t)` at `toRealMat M` and `toReal t` lies in the interval matrix `expW M t`: `t M_ij` between
its two directed products, `(M²)_ij` between the two directed dot products, `½ t²` between
`halfSqBounds`, and the corner hull of the last two.

## Inputs
* `M` – float matrix
* `t` – float time

## Hypotheses
* none

## Conclusion
* the exact second-order term lies in the float interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expW_mem (M : Mat 𝕋 n n) (t : 𝕋) : -- --- CONCL ---
    Real.MatExp.expW (toRealMat M) (toReal t) ∈ (MatExp.expW M t).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hh := MatExp.halfSqBounds_mem t
  have hd := Interval.mul_between_corners hh.1 hh.2 (dotDown_le (M i) fun k => M k j)
    (le_dotUp (M i) fun k => M k j)
  have hW : Real.MatExp.expW (toRealMat M) (toReal t) i j
      = toReal t * toReal (M i j)
        + toReal t ^ 2 / 2 * ∑ k, toReal (M i k) * toReal (M k j) := by
    simp [Real.MatExp.expW, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, toRealMat]
  rw [hW]
  simp only [MatExp.expW]
  constructor
  · exact le_trans (addDown_le_add _ _) (add_le_add (mulDown_le_mul _ _) hd.1)
  · exact le_trans (add_le_add (mul_le_mulUp _ _) hd.2) (add_le_addUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
