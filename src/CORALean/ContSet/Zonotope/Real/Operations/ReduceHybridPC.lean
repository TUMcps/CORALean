import CORALean.ContSet.Zonotope.Real.Operations.LineClBasis
import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA

/-!
# `Zonotope.reduceHybridPC`

HybridPC [1, Sec. III-C]: run line clustering and PCA, and return the reduced
zonotope of smaller volume. Both reductions share Girard's partition and so
share what they keep; they differ in the basis the dropped block is boxed along,
and the volume that decides is the one of eq. 7 at that block (`lineClVolume`).
Ties go to PCA, the robust one of the two. Noncomputable, as `pcaBasis` is.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The better of `reduceLineCl` and `reducePCA` by volume, and nothing at all at
order `o` or below. -/
noncomputable def Zonotope.reduceHybridPC (Z : Zonotope (Vec ℝ n)) (o : ℕ) (ξ : ℝ)
    (fuel runs : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then
    let split := Z.girardSplit o hlt
    let Llc := Z.lineClBasis split ξ fuel runs                      -- LineCl
    let U := Z.pcaBasis split                                       -- PCA
    if Z.lineClVolume split Llc < Z.lineClVolume split U then Z.reduceByBasis split Llc
    else Z.reduceByBasis split U                                    -- smaller volume
  else Z


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
