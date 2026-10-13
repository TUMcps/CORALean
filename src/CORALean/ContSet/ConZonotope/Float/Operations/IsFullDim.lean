import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
import CORALean.ContSet.Zonotope.Float.Operations.BallB

/-!
# `ConZonotope.isFullDim`, over a floating-point scalar

CORA's `@conZonotope/isFullDim` asks for `rank(G null(A)) = n`, which ignores that `|ξ| ≤ 1` and
`A ξ = b` can pin the factors. A sound test certifies the real property instead: with a
coefficient point `β₀` and a right inverse `H` of the generator matrix that the caller proposes,
`ConZonotope.interiorCert` puts a box of positive radius around `c + G β₀` inside the set, at the
margin `ConZonotope.interiorMargin`. The error box must be nonempty. `true` proves an interior
point; `false` refutes nothing.
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

def ConZonotope.isFullDim (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (H : Mat 𝕋 cZ.h n)
    (β₀ : Vec 𝕋 cZ.h) : Bool :=
  let δ := cZ.interiorMargin β₀
  cZ.interiorCert H β₀ δ (Zonotope.ballB H δ)
    && (List.finRange n).all fun i => le (cZ.E.inf i) (cZ.E.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
