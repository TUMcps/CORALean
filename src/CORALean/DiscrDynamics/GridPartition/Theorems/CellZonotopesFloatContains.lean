module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellZonotopesFloat
public import CORALean.DiscrDynamics.GridPartition.Theorems.CellIntervalsFloatNominal
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `GridPartition.cellZonotopes` contains the exact layer's boxes

The zonotope of a float box contains that box (`Interval.zonotope_contains`), and the float boxes
read back as the exact layer's, so each zonotope contains the box of `cellIntervals` for its cell.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* none

## Conclusion
* each zonotope contains the exact layer's box of its cell
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

theorem GridPartition.cellZonotopes_contains (P : GridPartition 𝕋 n) (cs : List ℕ) :
    List.Forall₂ (fun S Z => S ⊆ Z.construct)
      ((P.nominal.cellIntervals cs).map Real.Interval.construct) (P.cellZonotopes cs) := by
  -- each float box is contained in its zonotope
  rw [← GridPartition.cellIntervals_nominal, GridPartition.cellZonotopes, List.map_map,
    List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun B _ => Interval.zonotope_contains B

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
