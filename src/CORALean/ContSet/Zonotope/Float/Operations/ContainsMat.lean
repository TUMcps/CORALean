module

public import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint
public import CORALean.ContSet.Zonotope.Float.Operations.Vec

@[expose] public section

/-!
# `Zonotope.containsMat`, over a floating-point scalar

CORA's `@matZonotope/contains` of matrices: every matrix of the list, stacked column by column,
certified inside the stacked zonotope `zonotope(matZ)` by `Zonotope.containsPoint`, with the right
inverse `H` of the stacked generators that the caller proposes. Stacking moves entries only.
Sufficient only: `true` proves that every matrix is a member, `false` refutes nothing. CORA solves
a linear program per matrix and accepts a matrix within its tolerance outside.

## Inputs
* `Z` – matrix zonotope
* `H` – candidate right inverse of the stacked generators
* `S` – matrices

## Output
* true when every matrix is certified inside the matrix zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every matrix of `S`, stacked, certified in `zonotope(matZ)`. -/
def Zonotope.containsMat (Z : Zonotope (Mat 𝕋 m n)) (H : Mat 𝕋 Z.h (n * m))
    (S : Fin p → Mat 𝕋 m n) : Bool :=
  let V := Z.vec                                                          -- `zonotope(matZ)`
  let stack : Mat 𝕋 m n → Vec 𝕋 (n * m) := fun M q =>
    M (finProdFinEquiv.symm q).2 (finProdFinEquiv.symm q).1               -- `M(:)`
  (List.finRange p).all fun k => V.containsPoint H (stack (S k))         -- each matrix inside

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
