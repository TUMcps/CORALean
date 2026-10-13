import CORALean.ContSet.Zonotope.Float.Operations.DominantDirections
import CORALean.ContSet.Zonotope.Real.Theorems.ParallelotopeOuter

/-!
# The dominant directions enclose, when they are invertible

An answer `P` of `Zonotope.dominantDirections` whose stored entries form an invertible matrix
spans a parallelotope `P box(P⁻¹ Z)` holding the zonotope the stored floats describe [1, Prop. 8],
`Zonotope.parallelotope_outer`, which holds for any invertible `P`. So the rounded rankings that
chose `P` cost tightness only. As over ℝ the condition is not automatic: nothing tests that the
answer has full rank. The statement is about the nominal zonotope, as CORA's `G` has no error term.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_outer (Z : Zonotope (Vec 𝕋 n)) (a b : ℕ) (P : Mat 𝕋 n n)
    (_ : Z.dominantDirections a b = some P) (hP : IsUnit (toRealMat P).det) :
    nominalSet Z ⊆ ((nominal Z).parallelotope (toRealMat P)).construct :=
  CORALean.Real.Zonotope.parallelotope_outer hP (nominal Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
