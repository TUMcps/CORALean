module

public import CORALean.DiscrDynamics.GridPartition.GridPartition

@[expose] public section

/-!
# `DiscrDynamics/GridPartition/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n : ℕ}


-- ===============================  `GridPartition.IsWellFormed`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every dimension has a segment, and its dividers do not decrease. -/
def GridPartition.IsWellFormed (P : GridPartition n) : Prop :=
  ∀ j, 0 < P.nrOfSegments j ∧
    ∀ a b, a ≤ b → b ≤ P.nrOfSegments j → P.dividers j a ≤ P.dividers j b


-- ===============================  `GridPartition.Proportions`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `[iS, iProp]`: the cells found, led by `0`, and the share of the set in each. -/
structure GridPartition.Proportions where
  iS : List ℕ
  iProp : List ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
