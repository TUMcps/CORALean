module

public import CORALean.ContSet.Interval.Real.Definitions.ContainsMat
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# Without tolerance, `Interval.ContainsMat` is membership

At `tol = 0` the tests `inf < M`, `|inf - M| ≤ 0` collapse to `inf ≤ M`, and likewise for the
upper end; the emptiness test of a column then follows from `M` being in it.

## Inputs
* `A` – interval matrix
* `M` – real matrix

## Hypotheses
* none

## Conclusion
* containment with zero tolerance is membership
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `contains(intMat, M, 'exact', 0)` holds exactly for the members of the box. -/
theorem Interval.matContains_zero_iff (A : Interval (Mat ℝ m n)) (M : Mat ℝ m n) : -- --- CONCL ---
    A.ContainsMat M 0 ↔ M ∈ A.construct := by -- --- PROOF ---
  rw [Interval.mem_mat_iff]
  constructor
  · -- every test at tolerance `0` says `inf ≤ M` or `M ≤ sup`
    intro h i j
    obtain ⟨-, h2⟩ := h j
    obtain ⟨h3, h4⟩ := h2 i
    refine ⟨?_, ?_⟩
    · rcases h3 with h | h | h
      · linarith
      · have := abs_nonpos_iff.mp h; linarith
      · simp only [zero_mul] at h; have := abs_nonpos_iff.mp h; linarith
    · rcases h4 with h | h | h
      · linarith
      · have := abs_nonpos_iff.mp h; linarith
      · simp only [zero_mul] at h; have := abs_nonpos_iff.mp h; linarith
  · -- membership gives the tests, and the nonempty columns
    intro h j
    refine ⟨fun i => (h i j).1.trans (h i j).2, fun i => ⟨?_, ?_⟩⟩
    · rcases (h i j).1.lt_or_eq with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by rw [h']; simp))
    · rcases (h i j).2.lt_or_eq with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by rw [h']; simp))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
