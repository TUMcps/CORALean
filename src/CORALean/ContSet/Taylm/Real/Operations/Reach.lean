module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds

@[expose] public section

/-!
# How far a Taylor model reaches from a point

`max(|lo - c|, |hi - c|)` for the range `[lo, hi]`: a bound on `|f t - c|`, the quantity
the Lagrange remainder is a power of.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reach (T : Taylm n) (c : ℝ) : ℝ := max |T.bounds.inf - c| |T.bounds.sup - c|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
