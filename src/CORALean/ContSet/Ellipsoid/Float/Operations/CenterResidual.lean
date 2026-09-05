import CORALean.ContSet.Interval.Float.Operations.Residual

/-!
# `Ellipsoid.centerResidual`

Storing the lower of the two directed roundings of a centre sum leaves this
much to pay into the box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Ellipsoid.centerResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

end CORALean.Float
