module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.S2iI2s
public import CORALean.DiscrDynamics.GridPartition.Theorems.S2iMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sS2i
public import CORALean.DiscrDynamics.GridPartition.Operations.Basic
public import CORALean.DiscrDynamics.GridPartition.Definitions.Basic

@[expose] public section

/-!
# `DiscrDynamics/GridPartition/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n : ℕ}


-- ==========================  `GridPartition.cellInterval_nonempty`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A cell of a well-formed partition is a nonempty box. -/
theorem GridPartition.cellInterval_nonempty (P : GridPartition n) (hP : P.WellFormed) {c : ℕ}
    (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) (j : Fin n) :
    (P.cellInterval c).inf j ≤ (P.cellInterval c).sup j :=
  (hP j).2 _ _ (by omega) (GridPartition.i2s_mem P.nrOfSegments h2 h1 j).2


-- =============================  `GridPartition.mem_interval_iff`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point is in a box iff each coordinate is between the bounds. -/
theorem GridPartition.mem_interval_iff (I : Real.Interval (Vec ℝ n)) (x : Vec ℝ n) :
    x ∈ I.construct ↔ ∀ j, I.inf j ≤ x j ∧ x j ≤ I.sup j := Iff.rfl


-- ==============================  `GridPartition.nrOfCells_card`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `nrOfCells` counts the subscript vectors. -/
theorem GridPartition.nrOfCells_card (P : GridPartition n) :
    Fintype.card ((i : Fin n) → Fin (P.nrOfSegments i)) = P.nrOfCells := by
  simp [GridPartition.nrOfCells]


-- =================================  `GridPartition.tol_pos`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- The tolerance is positive. -/
theorem GridPartition.tol_pos : 0 < GridPartition.tol := by
  unfold GridPartition.tol; positivity

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
