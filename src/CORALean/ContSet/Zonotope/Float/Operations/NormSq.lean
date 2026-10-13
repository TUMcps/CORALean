import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.Norm

/-!
# `Zonotope.normSq` over a floating-point scalar

CORA's `@zonotope/norm_` at `type = 2` and `mode = 'ub'`: the norm of `interval(Z)`. There is
no float square root, so as for `Interval.normSq` the root is a certificate: this is the
squared length of the box, rounded up, and `normSq_le` takes a caller's `σ` with
`normSq ≤ σ·σ`. An upper bound only, not the norm.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/norm_` at `type = 2`, `mode = 'ub'`, as a squared length rounded up. -/
def Zonotope.normSq (Z : Zonotope (Vec 𝕋 n)) : 𝕋 := Z.interval.normSq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
