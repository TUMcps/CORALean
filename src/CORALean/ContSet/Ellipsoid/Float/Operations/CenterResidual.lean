module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.centerResidual`

Storing the lower of the two directed roundings of a center sum leaves this
much to pay into the box.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Ellipsoid.centerResidual (a b : Vec 𝕋 n) : Interval (Vec 𝕋 n) :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
