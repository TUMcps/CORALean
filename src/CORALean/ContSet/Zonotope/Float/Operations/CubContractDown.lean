module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp

@[expose] public section

/-!
# `Zonotope.cubContractDown`, the cubic contraction of three vectors rounded down

The primitive of the cubic map: for stored vectors `u`, `v`, `w` and a tensor `T`, a float
below `Σₖ uₖ · (vᵀ T{i,k} w)`. The middle vector `T{i,k} *ᵥ w` comes back as a pair of bounds
(`mulVecDown`, `mulVecUp`), `quadDown` against `v` turns it into bounds on the quadratic form, and
`quadDown` against `u` bounds the sum over `k`, the same two-step shape as `PolyZonotope.bilinGDown`
(a directed rounding does not compose through a product of unknown sign, so each step picks its
term by `minimum`). `Zonotope.cubMap`, `ConZonotope.cubMap`, `PolyZonotope.cubMap` and
`tensorMultiplication` all read their coefficients through it.

## Inputs
* `T` – cubic tensor
* `u` – weight vector
* `v` – left vector
* `w` – right vector
* `i` – output coordinate

## Output
* float below the weighted bilinear sum
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A float below `Σₖ uₖ · (vᵀ T{i,k} w)`. -/
def Zonotope.cubContractDown (T : Fin m → Fin n → Mat 𝕋 n n) (u v w : Vec 𝕋 n) (i : Fin m) :
    𝕋 :=
  -- the quadratic forms `vᵀ T{i,k} w`, from below and from above
  let qLo := fun k => PolyZonotope.quadDown v (mulVecDown (T i k) w) (mulVecUp (T i k) w)
  let qHi := fun k => PolyZonotope.quadUp v (mulVecDown (T i k) w) (mulVecUp (T i k) w)
  PolyZonotope.quadDown u qLo qHi

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
