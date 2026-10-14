module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainderFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# Every matrix within the bound lies in the float remainder box

Entry by entry, `abs_le` against `[-b, b]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.mem_expMatZonoRemainder {b : 𝕋} {D : Mat ℝ m m}
    (hD : ∀ i j, |D i j| ≤ toReal b) : D ∈ (MatExp.expMatZonoRemainder m b).construct := by
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  show toReal (neg b) ≤ D i j ∧ D i j ≤ toReal b
  rw [toReal_neg]
  exact abs_le.mp (hD i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
