import CORALean.ContSet.Interval.Real.Operations.MaxCos

/-!
# `Interval.cos`

CORA's `@interval/cos`, coordinate by coordinate: the upper bound is the largest cosine on the
range, `maxCos`, and the lower bound the negated largest cosine on the range shifted by `π`, as
`cos (x - π) = -cos x`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.cos (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => -Interval.maxCos (I.inf i - Real.pi) (I.sup i - Real.pi)
  sup := fun i => Interval.maxCos (I.inf i) (I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
