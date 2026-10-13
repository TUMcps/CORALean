module

public import CORALean.ContSet.Interval.Real.Operations.EBoxConstruct
public import CORALean.ContSet.Interval.Real.Operations.Inf

@[expose] public section

/-!
# `Interval.Inf` is the full space

The box `(-∞, ∞)ⁿ` denotes every point of `ℝⁿ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.Inf_exact (n : ℕ) : (Interval.Inf n).construct = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
