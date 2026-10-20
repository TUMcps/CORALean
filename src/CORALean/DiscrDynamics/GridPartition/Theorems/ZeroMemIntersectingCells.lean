module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# A box leaving the state space puts `0` in `intersectingCells`

A point of `I` outside the box the partition covers makes the list end in `0`, the outside.

## Inputs
* `P` – grid partition
* `I` – box
* `x` – point

## Hypotheses
* `hxI` – point lies in the box
* `hx` – point lies outside the state space

## Conclusion
* the outside is among the returned cells
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- If `I` has a point outside the state space, `0` is in `intersectingCells P I`. -/
theorem GridPartition.zero_mem_intersectingCells (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) {x : Vec ℝ n} (hxI : x ∈ I.construct)
    (hx : x ∉ P.intervals.construct) : -- --- CONCL ---
    0 ∈ P.intersectingCells I := by -- --- PROOF ---
  rw [GridPartition.mem_interval_iff] at hxI hx
  push Not at hx
  obtain ⟨j, hj⟩ := hx
  have hout : ∃ j, I.inf j < P.dividers j 0 ∨ P.dividers j (P.nrOfSegments j) < I.sup j := by
    refine ⟨j, ?_⟩
    simp only [GridPartition.intervals] at hj
    by_cases h : P.dividers j 0 ≤ x j
    · right; have := hj h; have := (hxI j).2; linarith
    · left; push Not at h; have := (hxI j).1; linarith
  unfold GridPartition.intersectingCells
  split_ifs <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
