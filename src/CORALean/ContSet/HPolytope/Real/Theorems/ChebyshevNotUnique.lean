module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.EuclideanNorm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The Chebyshev center is not unique

[1, Sec. 4.3 (Chebyshev)]: the program [1, Eq. 19] can have several optimal centers, "an example
for this is a rectangle". For `[0, 2] × [0, 1]` the largest radius is `1/2` — the two rows
bounding the second coordinate allow no more — and both `(1/2, 1/2)` and `(3/2, 1/2)` attain it.

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

theorem HPolytope.chebyshev_not_unique : -- --- STMT ---
    ∃ (A : Mat ℝ 4 2) (b : Vec ℝ 4) (c₁ c₂ : Vec ℝ 2), c₁ ≠ c₂ ∧
      (∀ j, (A *ᵥ c₁) j + 1 / 2 * ‖A j‖₂ ≤ b j) ∧ (∀ j, (A *ᵥ c₂) j + 1 / 2 * ‖A j‖₂ ≤ b j) ∧
      ∀ (c : Vec ℝ 2) (r : ℝ), (∀ j, (A *ᵥ c) j + r * ‖A j‖₂ ≤ b j) →
        r ≤ 1 / 2 := by -- --- PROOF ---
  let A : Mat ℝ 4 2 := !![1, 0; -1, 0; 0, 1; 0, -1]
  have hA : ∀ x : Vec ℝ 2, A *ᵥ x = ![x 0, -x 0, x 1, -x 1] := fun x => by
    funext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
  -- every row is a unit vector
  have hn : ∀ j, ‖A j‖₂ = 1 := by
    intro j
    fin_cases j <;> simp [A, norm₂, Fin.sum_univ_two]
  refine ⟨A, ![2, 0, 1, 0], ![1 / 2, 1 / 2], ![3 / 2, 1 / 2], fun h => ?_, fun j => ?_,
    fun j => ?_, fun c r h => ?_⟩
  · have := congrFun h 0
    norm_num at this
  · rw [hn, hA]
    fin_cases j <;> norm_num
  · rw [hn, hA]
    fin_cases j <;> norm_num
  -- the rows `y ≤ 1` and `-y ≤ 0` leave room for `2 r ≤ 1` only
  · have h2 := h 2
    have h3 := h 3
    rw [hn, hA] at h2 h3
    simp at h2 h3
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
