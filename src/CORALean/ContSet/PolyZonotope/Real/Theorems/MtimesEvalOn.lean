import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapEvalOn

/-!
# `mtimes` carries the evaluation along with it

`map_evalOn` at `mulVecLin`, which is all `mtimes` is: the linear half of the
post operator of [1, Alg. 1] and the first of the three [1, Lemma 4] composes —
the one that is dependency preserving by an *equality* rather than an enclosure.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimes`'s evaluation at `B` is the matrix image of the original's. -/
theorem PolyZonotope.mtimes_evalOn (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n))
    (B : Set (Fin pZ.p → ℝ)) :
    (PolyZonotope.mtimes M pZ).evalOn B = (M *ᵥ ·) '' pZ.evalOn B :=
  PolyZonotope.map_evalOn (Matrix.mulVecLin M) pZ B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
