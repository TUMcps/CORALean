module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Basic
public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope

@[expose] public section

/-!
# `ProbZonotope.pyramid`

CORA's `pyramid(probZ, mArray, P)`: the confidence zonotopes `zonotope(probZ, mᵢ)` stacked like
the layers of a pyramid. Layer `i` contributes the density step `maxVal(i+1) - maxVal(i)`
(`pyramidLevels`) times the volume of `zonotope(probZ, mᵢ) ∩ P`: `probTotal` is the sum. CORA
takes the volume by `modVolume`, `volume` where that exists and otherwise the volume of the interval
hull, an over-estimate it warns about; the exact volume is used here, and `Theorems.PyramidOuter`
is only the stronger for the larger one. `P` is any set of Euclidean space, with Lebesgue measure,
and `mArray` is meant to descend, as the steps are negative for an ascending one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory WithLp

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.pyramid (P : ProbZonotope n) {k : ℕ} (mArray : Fin k → ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  let maxVal : Fin (k + 1) → ℝ := P.pyramidLevels mArray
  let msZ : Fin k → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => toLp 2 '' (P.zonotope (mArray i)).construct
  let Pint : Fin k → Set (EuclideanSpace ℝ (Fin n)) := fun i => msZ i ∩ Q
  let V : Fin k → ℝ := fun i => volume.real (Pint i)
  let probPartial : Fin k → ℝ := fun i => (maxVal i.succ - maxVal i.castSucc) * V i
  ∑ i, probPartial i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
