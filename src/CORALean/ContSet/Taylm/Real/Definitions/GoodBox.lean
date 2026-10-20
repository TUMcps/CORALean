module

public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The sub-boxes of the normalized box

Boxes whose four ends lie in `[-1, 1]`, the boxes [1, Sec. 4]'s optimizer works on for a model
over the normalized box; halving keeps them so.

## Inputs
* `B` – box

## Output
* proposition that all ends lie in the unit interval

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.GoodBox (B : Fin n → Interval ℝ) : Prop :=
  ∀ k, -1 ≤ (B k).inf ∧ (B k).inf ≤ 1 ∧ -1 ≤ (B k).sup ∧ (B k).sup ≤ 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
