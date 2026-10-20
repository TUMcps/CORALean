module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# A matrix zonotope multiplied from the right, exactly

The mirror of `matMulLeft_exact`, and a separate statement rather than a
corollary of it: matrix multiplication does not commute, so neither side follows
from the other.

## Inputs
* `p` – row count
* `q` – inner dimension
* `r` – column count
* `M` – matrix
* `Z` – matrix zonotope

## Hypotheses
* none

## Conclusion
* right multiplication is exact
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMulRight_exact {p q r : ℕ} (M : Mat ℝ q r) (Z : Zonotope (Mat ℝ p q)) :
    (· * M) '' Z.construct = (Zonotope.mapOf (matMulRight M) Z).construct :=
  Zonotope.map_exact (matMulRight M) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
