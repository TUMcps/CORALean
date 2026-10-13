module

public import CORALean.ContSet.Interval.Real.Operations.Sum2
public import CORALean.ContSet.Interval.Real.Theorems.Sum1Exact
public import CORALean.ContSet.Interval.Real.Theorems.TransposeExact

@[expose] public section

/-!
# `Interval.sum₂` is exactly the set of row sums

The row sums of a matrix are the column sums of its transpose, so `sum₁_exact` at the transposed
box gives it, again for a nonempty box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sum₂_exact {I : Interval (Mat ℝ m n)} (hI : I.IsNonempty) :
    I.sum₂.construct =
      (fun A : Mat ℝ m n => fun i => ∑ j, A i j) '' I.construct := by -- --- PROOF ---
  have hT : I.transpose.IsNonempty := fun p => hI (p.2, p.1)
  -- the row sums of `I` are the column sums of the transposed box
  have h := Interval.sum₁_exact hT
  rw [Interval.transpose_exact] at h
  ext y
  constructor
  · intro hy
    obtain ⟨B, ⟨A, hA, rfl⟩, hB⟩ := (Set.ext_iff.1 h y).1 hy
    exact ⟨A, hA, hB⟩
  · rintro ⟨A, hA, rfl⟩
    exact (Set.ext_iff.1 h _).2 ⟨A.transpose, ⟨A, hA, rfl⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
