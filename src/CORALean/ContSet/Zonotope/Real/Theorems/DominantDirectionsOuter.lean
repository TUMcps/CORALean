module

public import CORALean.ContSet.Zonotope.Real.Operations.DominantDirections
public import CORALean.ContSet.Zonotope.Real.Theorems.ParallelotopeOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.DominantDirectionsMemShortlist

@[expose] public section

/-!
# The dominant directions enclose, when they are invertible

An answer `P` of `dominantDirections` with `det P ≠ 0` spans a parallelotope `P box(P⁻¹ Z)`
holding `Z` [1, Prop. 8], `Zonotope.parallelotope_outer`. The condition is not automatic: the
filters never test that the answer has full rank (`priv_volumeFilter` gives a singular candidate
the score `inf` and still returns the first one when all are), see
`dominantDirections_det_eq_zero_of_orthogonal`.

## Inputs
* `Z` – zonotope
* `a` – length-filter size
* `b` – volume-filter size
* `P` – returned basis

## Hypotheses
* `_` – `P` is the returned basis
* `hP` – `P` invertible

## Conclusion
* `Z` lies in the parallelotope of `P`

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_outer (Z : Zonotope (Vec ℝ n)) (a b : ℕ) (P : Mat ℝ n n)
    (_ : Z.dominantDirections a b = some P) (hP : IsUnit P.det) :
    Z.construct ⊆ (Z.parallelotope P).construct :=
  Zonotope.parallelotope_outer hP Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
