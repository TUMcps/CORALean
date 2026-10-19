module

public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor

@[expose] public section

/-!
# A factor from above, computed and not trusted

CORA's conversions to generator form factor `Q = G Gᵀ` by its eigendecomposition, `G = V √D`. In
floats no factor is exact, so the factor proposed here errs upward: `cholFactor` of `Q` with each
diagonal entry raised by `2⁻²⁸` of itself, so that `G Gᵀ ≈ Q + τ` with `τ` about `2⁻²⁹` of each
diagonal entry, a diagonal margin the rounding errors cannot outweigh. Nothing about `G` is proved:
`isOuterFactor` checks `G Gᵀ - Q` in outward rounding.

## Inputs
* `Q` – shape matrix

## Output
* proposed factor `G` with `G Gᵀ` slightly above `Q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A proposed `G` with `G Gᵀ` slightly above `Q`. -/
def Ellipsoid.outerFactor (Q : Mat 𝕋 n n) : Mat 𝕋 n n :=
  -- `Q` with its diagonal raised by `2⁻²⁸` of itself
  let Q' : Mat 𝕋 n n := fun i j =>
    if i = j then addUp (Q i i) (half^[28] (absolute (Q i i))) else Q i j
  Ellipsoid.cholFactor 64 Q'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
