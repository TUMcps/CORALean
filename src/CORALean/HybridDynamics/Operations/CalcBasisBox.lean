module

public import CORALean.Global.ExactScalar
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Location.calcBasisBox`

CORA's `@location/calcBasis.m` at `options.enclose{i} = 'box'`: `B{i} = eye(sys.nrOfDims)`, the
identity, so the guard intersection is enclosed in the coordinate directions. The `'pca'` case
(the left singular vectors of the reachable set's generators, `svd([-G, G])`) and the `'flow'`
case (a Gram-Schmidt basis of the flow direction) are not modelled, and `calcBasis` returns one
basis per entry of `options.enclose`, of which this is the `'box'` entry.

## Inputs
* `𝕋` – scalar type
* `n` – dimension

## Output
* identity matrix as the basis
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eye(n)`, the `'box'` basis of `n` dimensions. Generic over the scalar: it places `0` and `1`
only, which every float format holds exactly. -/
def Location.calcBasisBox (𝕋 : Type) [Scalar 𝕋] [ExactScalar 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
