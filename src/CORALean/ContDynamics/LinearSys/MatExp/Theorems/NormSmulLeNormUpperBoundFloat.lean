import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax

/-!
# A step's matrix, scaled, is normed below the float bound of its box

`r • M` lies in `Interval.smul r r A` (`smul_outer`), its norm is below that
box's dominating matrix's (`norm_le_absMax`), and that below `normUpperBound`.
The one bound every remainder of a step is taken at, so the order admissible for
one is admissible for all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_smul_le_normUpperBound (A : Interval (Mat 𝕋 n n)) (r : 𝕋) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) :
    ‖toReal r • M‖ ≤ toReal (MatExp.normUpperBound (Interval.smul r r A)) :=
  le_trans (Real.Interval.norm_le_absMax (Interval.smul_outer le_rfl le_rfl A hM))
    (MatExp.norm_absMax_le_normUpperBound _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
