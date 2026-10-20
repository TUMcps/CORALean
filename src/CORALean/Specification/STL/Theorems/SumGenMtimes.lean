module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The weighted generators of a linear map

The generators of `MZ` are those of `Z` mapped by `M` ([1, Prop. 1]), so a weighted sum of them
is `M` applied to the weighted sum over `Z`.

## Inputs
* `M` – matrix
* `Z` – zonotope
* `f` – generator weights

## Hypotheses
* none

## Conclusion
* the weighted generators of the image are the image of the weighted generators

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.sumGen_mtimes (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) (f : ℕ → ℝ) :
    ∑ k : Fin (Zonotope.mtimes M Z).h, f k • (Zonotope.mtimes M Z).G k
      = M *ᵥ ∑ k : Fin Z.h, f k • Z.G k := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
