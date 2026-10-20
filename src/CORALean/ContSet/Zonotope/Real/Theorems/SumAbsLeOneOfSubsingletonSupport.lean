module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A row with one nonzero entry of modulus at most `1`

A row of `T` that is nonzero in at most one place, and there at most `1` in modulus, has
absolute sum at most `1`: the row condition `‖T‖∞ ≤ 1` of [1, Eq. (1)] for the heuristic
methods, whose `T` has one `±1` or `0` per row.

## Inputs
* `r` – length
* `f` – vector

## Hypotheses
* `hu` – at most one nonzero entry
* `hb` – entries at most one in absolute value

## Conclusion
* the absolute sum is at most one

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- At most one nonzero entry, each of modulus at most `1`: the absolute sum is at most `1`. -/
theorem Zonotope.sum_abs_le_one_of_subsingleton_support {r : ℕ} (f : Fin r → ℝ)
    (hu : ∀ i i', f i ≠ 0 → f i' ≠ 0 → i = i') (hb : ∀ i, |f i| ≤ 1) :
    ∑ i, |f i| ≤ 1 := by -- --- PROOF ---
  by_cases h : ∃ i0, f i0 ≠ 0
  · -- the only term that can be nonzero
    obtain ⟨i0, hi0⟩ := h
    rw [Finset.sum_eq_single i0 (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)]
    · exact hb i0
    · by_contra hne
      exact hi (hu i i0 (abs_pos.mp (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne))) hi0)
  · -- every entry is zero
    push Not at h
    simp [h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
