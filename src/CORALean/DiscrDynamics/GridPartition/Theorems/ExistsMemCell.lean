module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.S2iMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sS2i
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# The cells cover the state space

A point of the box a well-formed partition covers lies in some cell: in each dimension take
the last divider not above it.

## Inputs
* `P` – grid partition
* `x` – point

## Hypotheses
* `hP` – partition well formed
* `hx` – point lies in the state space

## Conclusion
* the point lies in some cell
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Inside one dimension: a point between the first and last divider is between two neighbours. -/
theorem GridPartition.aux_exists_cell (d : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    (hd : ∀ a b, a ≤ b → b ≤ m → d a ≤ d b) {t : ℝ} (h0 : d 0 ≤ t) (h1 : t ≤ d m) :
    ∃ k, 1 ≤ k ∧ k ≤ m ∧ d (k - 1) ≤ t ∧ t ≤ d k := by -- --- PROOF ---
  induction m, hm using Nat.le_induction with
  | base => exact ⟨1, le_rfl, le_rfl, h0, h1⟩
  | succ m hm ih =>
    by_cases h : t ≤ d m
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (fun a b hab hb => hd a b hab (by omega)) h
      exact ⟨k, hk1, by omega, hk3, hk4⟩
    · push Not at h
      exact ⟨m + 1, by omega, le_rfl, by simpa using h.le, h1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the state space lies in a cell of a well-formed partition. -/
theorem GridPartition.exists_mem_cell (P : GridPartition n) (hP : P.WellFormed) {x : Vec ℝ n}
    (hx : x ∈ P.intervals.construct) :
    ∃ c, 1 ≤ c ∧ c ≤ P.nrOfCells ∧ x ∈ (P.cellInterval c).construct := by -- --- PROOF ---
  rw [GridPartition.mem_interval_iff] at hx
  have : ∀ j, ∃ k, 1 ≤ k ∧ k ≤ P.nrOfSegments j ∧
      P.dividers j (k - 1) ≤ x j ∧ x j ≤ P.dividers j k := fun j =>
    GridPartition.aux_exists_cell (P.dividers j) (hP j).1 (hP j).2 (hx j).1 (hx j).2
  choose sub h1 h2 h3 h4 using this
  have hin : ∀ j, 0 < sub j ∧ sub j ≤ P.nrOfSegments j := fun j => ⟨h1 j, h2 j⟩
  refine ⟨GridPartition.s2i P.nrOfSegments sub, (GridPartition.s2i_mem _ hin).1,
    (GridPartition.s2i_mem _ hin).2, ?_⟩
  rw [GridPartition.mem_interval_iff]
  intro j
  simp only [GridPartition.cellInterval, GridPartition.i2s_s2i _ hin]
  exact ⟨h3 j, h4 j⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
