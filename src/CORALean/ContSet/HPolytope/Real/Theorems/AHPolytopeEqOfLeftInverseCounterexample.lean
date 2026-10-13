import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases

/-!
# `[1, Eq. 4]` fails for a non-square map

`X = (1, 0)ᵀ` maps `[-1, 1]` onto a segment of the first axis of `ℝ²`, and `X† = (1, 0)`
has `X† X = I`. The printed right-hand side `{y | H X† y ≤ h}` is the strip `|y₁| ≤ 1`,
which contains `(0, 1)`, off the segment.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_eq_of_leftInverse_counterexample :
    ∃ (X : Mat ℝ 2 1) (Xd : Mat ℝ 1 2) (H : Mat ℝ 2 1) (h : Vec ℝ 2), Xd * X = 1 ∧
      HPolytope.ahPolytope 0 X (HPolytope.ineqs H h)
        ≠ {y | (H * Xd) *ᵥ y ≤ h + (H * Xd) *ᵥ 0} := by -- --- PROOF ---
  refine ⟨!![1; 0], !![1, 0], !![1; -1], ![1, 1], ?_, fun heq => ?_⟩
  · ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  -- `(0, 1)` satisfies the printed inequalities and is not `X p`
  · have hmem : (![0, 1] : Vec ℝ 2) ∈ {y : Vec ℝ 2 |
        ((!![1; -1] : Mat ℝ 2 1) * (!![1, 0] : Mat ℝ 1 2)) *ᵥ y
          ≤ ![1, 1] + ((!![1; -1] : Mat ℝ 2 1) * (!![1, 0] : Mat ℝ 1 2)) *ᵥ 0} := by
      intro i; fin_cases i <;> norm_num [mulVec, dotProduct, Matrix.mul_apply]
    rw [← heq] at hmem
    obtain ⟨p, -, hp⟩ := hmem
    have := congrFun hp 1
    norm_num [mulVec, dotProduct] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
