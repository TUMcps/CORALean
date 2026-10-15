module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWOuter
public import CORALean.ContSet.Interval.Real.Theorems.ExactSquareOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemOfCenterRadius
public import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe

@[expose] public section

/-!
# `dependentTerms` contains the exact terms of every member

The square scaled by `r²` and `I + M r + ½ M² r²` of every `M` in the box lie in `intSq` and
`intH`: the first is `exactSquare_outer`, the second `expW_mem_expIntervalW`, and rebuilding an
interval from its centre and radius, with the identity added to the centre, changes neither.
Tightness of both is `exactSquare_entry_exact` and `expIntervalW_attained`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both outputs of `dependentTerms` contain the true value for every member of the box. -/
theorem MatExp.dependentTerms_outer (A : Interval (Mat ℝ n n)) (r : ℝ) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) :
    r ^ 2 • (M * M) ∈ (MatExp.dependentTerms A r).intSq.construct ∧
      1 + MatExp.expW M r ∈ (MatExp.dependentTerms A r).intH.construct := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · -- `M * M` is within the radius of the centre of the exact square, and `r²` scales both
    rw [MatExp.dependentTerms, Interval.mem_ofCenterRadius]
    intro p
    have h := Interval.abs_sub_center_le (Interval.exactSquare_outer A hM) p
    simp only [Entrywise.entry_smul, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg r)
  · -- the same for `W(r)` and the identity added to both centre and member
    rw [MatExp.dependentTerms, Interval.mem_ofCenterRadius]
    intro p
    have h := Interval.abs_sub_center_le (MatExp.expW_mem_expIntervalW A r hM) p
    simp only [Entrywise.entry_add]
    convert h using 2
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
