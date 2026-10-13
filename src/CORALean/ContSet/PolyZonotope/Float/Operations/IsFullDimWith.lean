import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.Zonotope.Float.Operations.BallCert
import CORALean.ContSet.Zonotope.Float.Operations.BallB

/-!
# `PolyZonotope.isFullDimWith`, over a floating-point scalar

CORA's `@polyZonotope/isFullDim` asks for `rank([G GI]) = n`, which is necessary for a nonempty
interior and not sufficient (the arc `(a, a²)` passes). A sound test certifies the real property
instead: at the factors `α = 0` the set contains the translate of the zonotope spanned by the
independent generators `GI`, so a right inverse `H` of `GI` that the caller proposes and the check
of `Zonotope.ballCert` accepts puts a box of positive radius inside the set. The error box must be
nonempty. `true` proves an interior point; `false` refutes nothing, a set with full-dimensional
dependent part and no independent generators included.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.isFullDimWith (pZ : PolyZonotope (Vec 𝕋 n)) (H : Mat 𝕋 pZ.q n) : Bool :=
  Zonotope.ballCert (fun i j => pZ.GI j i) H (Zonotope.ballB H one) one
    && (List.finRange n).all fun i => le (pZ.err.inf i) (pZ.err.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
