module

public import CORALean.ContSet.Interval.Real.Operations.MatVolume
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# `Interval.matVolume` is the Lebesgue volume

The matrices of a box, read as functions `Fin m → Fin n → ℝ` with the product measure, form the
product over rows of the products over columns of the entry intervals; `Measure.pi` gives the
product of the volumes, and each row is `Real.volume_Icc_pi`.

## Inputs
* `A` – interval matrix

## Hypotheses
* none

## Conclusion
* the matrix volume is the Lebesgue volume of the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Lebesgue volume of the box, as matrices read as functions, is `matVolume`. -/
theorem Interval.matVolume_eq (A : Interval (Mat ℝ m n)) :
    MeasureTheory.volume {f : Fin m → Fin n → ℝ | (Matrix.of f : Mat ℝ m n) ∈ A.construct}
      = A.matVolume := by -- --- PROOF ---
  have hc : {f : Fin m → Fin n → ℝ | (Matrix.of f : Mat ℝ m n) ∈ A.construct}
      = Set.pi Set.univ (fun i => Set.Icc (A.inf i) (A.sup i)) := by
    ext f
    simp only [Set.mem_setOf_eq, Interval.mem_mat_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, Pi.le_def, Matrix.of_apply]
    exact ⟨fun h i => ⟨fun j => (h i j).1, fun j => (h i j).2⟩,
      fun h i j => ⟨(h i).1 j, (h i).2 j⟩⟩
  rw [hc, MeasureTheory.volume_pi_pi]
  exact Finset.prod_congr rfl fun i _ => Real.volume_Icc_pi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
