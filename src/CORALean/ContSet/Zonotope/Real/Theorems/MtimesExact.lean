module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# A matrix times a zonotope is exact

`map_exact` at `A *ᵥ ·`, which is the case reachability runs. No `mtimes_outer`:
the float `mtimes` pays its rounding into the error box, so it reproves this
against the rounded generators rather than composing with it.

## Inputs
* `n` – dimension
* `m` – output dimension
* `M` – matrix
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the image of `Z` equals the zonotope of `mtimes`
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' Z.construct = (Zonotope.mtimes M Z).construct :=
  Zonotope.map_exact (Matrix.mulVecLin M) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
