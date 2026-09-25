import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `Zonotope.mtimesIntervalMat`, over a floating-point scalar

The float counterpart of `Real.Zonotope.mtimesIntervalMat`: no fresh generator
per coordinate, unlike the exact layer, since a float representation pays every
rounding into the error box instead. `Zonotope.mtimes` already handles the
centre matrix `Interval.centreMat`; what is left over — a matrix known only to
within `Interval.matResidual` acting on a point known only to within
`Zonotope.absBoundError` — is itself a box-times-box product, so
`Interval.mtimesIntervalMat` computes it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mid(M) * Z`, rounded into `Z`'s own box the way `mtimes` rounds a plain
matrix, plus a box for what the interval matrix's radius can still add. -/
def Zonotope.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m :=
  { Zonotope.mtimes (Interval.centreMat IM) Z with
    E := (Zonotope.mtimes (Interval.centreMat IM) Z).E.plus
      (Interval.mtimesIntervalMat (Interval.matResidual IM.inf IM.sup (Interval.centreMat IM))
        (Interval.symmetric fun j => Zonotope.absBoundError Z j)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
