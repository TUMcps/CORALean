module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellCenterFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.DiscrDynamics.GridPartition.Operations.CellCenter

@[expose] public section

/-!
# `GridPartition.cellCenter` holds the exact midpoints

Each midpoint the exact layer returns lies in the bracket of the same cell, because the real
midpoint of the stored bounds is between the sum rounded down and up. Both lists are empty
together when a cell is out of range.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* none

## Conclusion
* the exact midpoints lie in the float brackets, cell for cell
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

theorem GridPartition.cellCenter_mem (P : GridPartition 𝕋 n) (cs : List ℕ) : -- --- CONCL ---
    List.Forall₂ (fun z B => z ∈ B.construct) (P.nominal.cellCenter cs)
      (P.cellCenter cs) := by -- --- PROOF ---
  unfold GridPartition.cellCenter CORALean.GridPartition.cellCenter
  by_cases h : ∀ c ∈ cs, 0 < c ∧ c ≤ P.nrOfCells
  · -- every cell is in range: compare the midpoint of each cell with its bracket
    have h' : ∀ c ∈ cs, 0 < c ∧ c ≤ P.nominal.nrOfCells := h
    rw [if_pos h', if_pos h, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun c _ => ?_
    -- the real midpoint of the stored bounds is between the two roundings
    intro j
    have e : (P.cellInterval c).nominal.center j = (toReal ((P.cellInterval c).inf j)
        + toReal ((P.cellInterval c).sup j)) / 2 := by
      show (2:ℝ)⁻¹ * (toReal ((P.cellInterval c).inf j) + toReal ((P.cellInterval c).sup j)) = _
      ring
    have h1 := (P.cellInterval c).centerLo_le j
    have h2 := (P.cellInterval c).center_ge j
    rw [e] at h1 h2
    exact ⟨h1, h2⟩
  · have h' : ¬∀ c ∈ cs, 0 < c ∧ c ≤ P.nominal.nrOfCells := h
    rw [if_neg h', if_neg h]
    exact List.Forall₂.nil

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
