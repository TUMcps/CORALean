module

public import CORALean.ContSet.Interval.Float.Operations.Inf
public import CORALean.ContSet.Interval.Float.Operations.EBoxConstruct

@[expose] public section

/-!
# `Interval.Inf` is exact, over a floating-point scalar

No bound is stored, so the box denotes all of `ℝⁿ`; nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
