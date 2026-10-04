import CORALean.ContSet.Zonotope.Float.Operations.BallCert
import CORALean.ContSet.Zonotope.Float.Operations.BallB
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.isFullDimWith`, over a floating-point scalar

CORA's `@zonotope/isFullDim` asks for `rank(G) = n`, which rounding cannot decide. A sound test
checks instead a right inverse `H` of the generator matrix that the caller proposes: if `G H` is
within `1/2` of the identity in every absolute row sum (`Zonotope.ballCert`, products rounded
upward) then every vector in a box of positive radius around the centre is `G β` with
`|βⱼ| ≤ 1`, a box inside the zonotope. The error box must be nonempty (`inf ≤ sup` by `le`).
`true` proves an interior point; `false` refutes nothing.
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

def Zonotope.isFullDimWith (Z : Zonotope 𝕋 n) (H : Mat 𝕋 Z.h n) : Bool :=
  Zonotope.ballCert Z.G H (Zonotope.ballB H one) one
    && (List.finRange n).all fun i => le (Z.E.inf i) (Z.E.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
