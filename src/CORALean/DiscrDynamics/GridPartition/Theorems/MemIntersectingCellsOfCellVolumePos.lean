module

public import CORALean.DiscrDynamics.GridPartition.Theorems.IntersectingCellsOuter

@[expose] public section

/-!
# A cell with volume in the set is returned

A cell sharing positive volume with a set inside the box `I` meets `I`, so `intersectingCells`
lists it: the volume-weighted `exactIntersectingCells` loses no cell by taking its candidates there.

## Inputs
* `P` – grid partition
* `I` – box
* `K` – set inside the box
* `c` – cell number

## Hypotheses
* `hn` – dimension nonzero
* `hK` – the set lies in the box
* `h1` – cell number at least one
* `h2` – cell number within the cell count
* `hv` – the set has positive volume in the cell

## Conclusion
* the cell is returned
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A cell holding positive volume of `K ⊆ I` is among `intersectingCells P I`. -/
theorem GridPartition.mem_intersectingCells_of_cellVolume_pos (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) (hn : n ≠ 0) {K : Set (Vec ℝ n)} (hK : K ⊆ I.construct)
    {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) (hv : 0 < P.cellVolume K c) :
    c ∈ P.intersectingCells I := by -- --- PROOF ---
  -- positive volume means the intersection is not empty
  have hne : (K ∩ (P.cellInterval c).construct).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    simp only [GridPartition.cellVolume, GridPartition.volumeOf, hempty,
      MeasureTheory.measure_empty, ENNReal.toReal_zero] at hv
    exact lt_irrefl _ hv
  obtain ⟨x, hxK, hxc⟩ := hne
  exact GridPartition.intersectingCells_outer P I hn h1 h2 (hK hxK) hxc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
