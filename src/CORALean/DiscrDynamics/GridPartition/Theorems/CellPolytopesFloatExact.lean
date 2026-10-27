module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellPolytopesFloat
public import CORALean.DiscrDynamics.GridPartition.Theorems.CellIntervalsFloatNominal
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalHPolytopeExact

@[expose] public section

/-!
# `GridPartition.cellPolytopes` denotes the exact layer's boxes

The polytope of a float box denotes exactly that box (`Interval.hPolytope_exact`), and the float
boxes read back as the exact layer's, so the polytopes denote the boxes of `cellIntervals`, one
for one.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* none

## Conclusion
* the polytopes denote exactly the exact layer's boxes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GridPartition.cellPolytopes_exact (P : GridPartition 𝕋 n) (cs : List ℕ) :
    (P.cellPolytopes cs).map (fun Q => Q.construct) =
      (P.nominal.cellIntervals cs).map Real.Interval.construct := by
  rw [← GridPartition.cellIntervals_nominal, GridPartition.cellPolytopes, List.map_map,
    List.map_map]
  exact List.map_congr_left fun B _ => Interval.hPolytope_exact B

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
