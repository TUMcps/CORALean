module

public import CORALean.Specification.STL.Operations.TreeMinimumTimeFrom

@[expose] public section

/-!
# The offset of minimumTime is added

Starting `minimumTime`'s recursion at the offset `time` adds `time` to the result.

## Inputs
* `φ` – formula
* `time` – offset

## Hypotheses
* none

## Conclusion
* the offset is added to the earliest time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.minimumTimeFrom_eq_add (φ : STL.Tree NNReal ℝ n) (time : ℝ≥0) : -- --- CONCL ---
    φ.minimumTimeFrom time = time + φ.minimumTimeFrom 0 := by -- --- PROOF ---
  induction φ generalizing time with
  | tt | ff | cmp => simp [STL.Tree.minimumTimeFrom]
  | not φ ih => exact ih time
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.minimumTimeFrom, ihφ time, ihψ time, min_add_add_left]
  | next a φ ih =>
    simp only [STL.Tree.minimumTimeFrom, ih (a + time), ih (a + 0)]
    ring
  | «finally» a b φ ih | globally a b φ ih => simp only [STL.Tree.minimumTimeFrom]; ring
  | «until» a b φ ψ ihφ ihψ | release a b φ ψ ihφ ihψ => simp [STL.Tree.minimumTimeFrom]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
