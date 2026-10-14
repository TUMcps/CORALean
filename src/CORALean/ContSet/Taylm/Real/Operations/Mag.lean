module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds

@[expose] public section

/-!
# The magnitude of a Taylor model

The largest `|x|` over the constant part and the range: every point between the centre and
the range lies within it. The derivative bounds of `sinh`, `cosh`, `tanh`, `tan`, `atan`,
`asin` and `acos` are stated at this one number.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.mag (T : Taylm n) : ℝ :=
  max |T.constCoef| (max |T.bounds.inf| |T.bounds.sup|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
