import CORALean.ContSet.VPolytope.Float.Operations.Bordered
import CORALean.ContSet.Zonotope.Float.Operations.BallCert
import CORALean.ContSet.Zonotope.Float.Operations.BallB

/-!
# `VPolytope.isFullDimWith`, over a floating-point scalar

CORA's `@polytope/isFullDim` on vertices asks for the rank of the shifted vertices, which rounding
cannot decide. A sound test checks instead a right inverse `H` of the bordered vertex matrix
`[V; 1ᵀ]` (`VPolytope.bordered`) that the caller proposes: if `Zonotope.ballCert` accepts it, then
every `(y, 0)` within a certified radius `B` of the vertices' mean is `[V; 1ᵀ] λ'` with every
`|λ'ⱼ| ≤ δ`, and with `k δ ≤ 1` the weights `1/k + λ'ⱼ` are nonnegative and sum to one, so the
point is a convex combination of the vertices. The error box must be nonempty. `true` proves an
interior point; `false` refutes nothing.
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

def VPolytope.isFullDimWith (P : VPolytope (Vec 𝕋 n)) (H : Mat 𝕋 P.k (n + 1)) : Bool :=
  -- the coefficient bound `δ`, below `1 / k` after rounding, and the radius `B` it allows
  let δ : 𝕋 := half (divDown one (nsmulUp P.k one))
  Nat.ble 1 P.k && le (nsmulUp P.k δ) one
    && Zonotope.ballCert P.bordered H (Zonotope.ballB H δ) δ
    && (List.finRange n).all fun i => le (P.E.inf i) (P.E.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
