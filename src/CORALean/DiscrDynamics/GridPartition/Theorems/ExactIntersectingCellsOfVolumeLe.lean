module

public import CORALean.DiscrDynamics.GridPartition.Operations.ExactIntersectingCells

@[expose] public section

/-!
# A set of volume zero is entirely outside

CORA's `exactIntersectingCells` of a set whose volume is not positive: `iS = 0` and `iProp = 1`,
all of it counted as outside the partition, whether or not it lies inside.

## Inputs
* `P` – grid partition
* `X` – set

## Hypotheses
* `h` – set has no positive volume

## Conclusion
* the set is counted entirely outside
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A set of volume `0` (or `∞`) gets CORA's `iS = 0`, `iProp = 1`: all of it outside. -/
theorem GridPartition.exactIntersectingCells_of_volume_le (P : GridPartition n) (X : S n)
    (h : ¬ 0 < GridPartition.volumeOf (construct X)) :
    P.exactIntersectingCells X = ⟨[0], [1]⟩ := by
  unfold GridPartition.exactIntersectingCells; rw [if_neg h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
