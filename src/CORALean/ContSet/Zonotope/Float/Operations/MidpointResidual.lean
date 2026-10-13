module

public import CORALean.ContSet.Interval.Float.Operations.Residual
public import CORALean.ContSet.Zonotope.Float.Operations.Midpoint

@[expose] public section

/-!
# What storing the midpoint leaves to pay

Split out of `LinComb.lean` (issue #62): used again by `ConZonotope.linComb`
and by `MidpointMemResidual.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Storing the lower of the two directed midpoints leaves this much to pay. -/
def Zonotope.midpointResidual (a b : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  Interval.residual (fun i => half (addDown (a i) (b i)))
    (fun i => half (addUp (a i) (b i))) (Zonotope.midpoint a b)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
