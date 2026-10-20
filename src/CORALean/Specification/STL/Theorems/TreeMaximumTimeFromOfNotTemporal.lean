module

public import CORALean.Specification.STL.Operations.TreeMaximumTimeFrom
public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# A formula with no temporal operator needs no time

For a formula with no temporal operator `maximumTime.m` returns `time` at once; the recursion of
`STL.Tree.maximumTimeFrom` gives the same, so the test CORA makes first is not needed.

## Inputs
* `φ` – formula
* `time` – offset

## Hypotheses
* `h` – the formula has no temporal operator

## Conclusion
* the latest time is the offset
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

theorem STL.Tree.maximumTimeFrom_of_not_temporal (φ : STL.Tree n) (h : φ.temporal = false)
    (time : ℝ≥0) : -- --- CONCL ---
    φ.maximumTimeFrom time = time := by -- --- PROOF ---
  induction φ with
  | tt | ff | cmp => rfl
  | not φ ih => exact ih h
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.temporal, Bool.or_eq_false_iff] at h
    simp [STL.Tree.maximumTimeFrom, ihφ h.1, ihψ h.2]
  | _ => simp [STL.Tree.temporal] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
