import CORALean.ContSet.Interval.Float.Operations.Inf
import CORALean.ContSet.Interval.Float.Operations.EBoxConstruct

/-!
# `Interval.Inf` is exact, over a floating-point scalar

No bound is stored, so the box denotes all of `ℝⁿ`; nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.Inf_exact (n : ℕ) :
    (Interval.Inf n : Interval.EBox 𝕋 n).construct = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.construct]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
