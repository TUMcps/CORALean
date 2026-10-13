import CORALean.ContSet.HPolytope.Real.Theorems.InteriorNonemptyIffChebyshev
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# `[1, Eq. 18]` as printed reads the Chebyshev radius the wrong way round

The display says `degenerate(⟨A, b⟩) ← ⊤ if r > 0`. The interval `[0, 1] = {x ≤ 1, -x ≤ 0}`
admits the ball of radius `1/2` around `1/2`, so the optimal radius of [1, Eq. 19] is positive,
yet the interval has an interior. The text beside the display has it right — radius `0` means
degenerate — which is `HPolytope.ineqs_interior_nonempty_iff`.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_degenerate_chebyshev_counterexample :
    ∃ (A : Mat ℝ 2 1) (b : Vec ℝ 2) (c : Vec ℝ 1) (r : ℝ), 0 < r ∧
      (∀ j, (A *ᵥ c) j + r * ‖A j‖₂ ≤ b j) ∧
      (interior (HPolytope.ineqs A b).construct).Nonempty := by -- --- PROOF ---
  -- each row has Euclidean length one
  have hn : ∀ v : Vec ℝ 1, (v = ![1] ∨ v = ![-1]) → ‖v‖₂ = 1 := by
    rintro v (rfl | rfl) <;> simp [norm₂]
  have hfeas : ∀ j : Fin 2, (!![1; -1] *ᵥ ![1 / 2]) j + 1 / 2 * ‖(!![1; -1] : Mat ℝ 2 1) j‖₂
      ≤ ![1, 0] j := by
    intro j
    fin_cases j
    · rw [hn _ (Or.inl (by ext i; fin_cases i; rfl))]
      simp [mulVec, dotProduct]
      norm_num
    · rw [hn _ (Or.inr (by ext i; fin_cases i; rfl))]
      simp [mulVec, dotProduct]
  refine ⟨!![1; -1], ![1, 0], ![1 / 2], 1 / 2, by norm_num, hfeas, ?_⟩
  exact (HPolytope.ineqs_interior_nonempty_iff _ _).mpr ⟨_, _, by norm_num, hfeas⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
