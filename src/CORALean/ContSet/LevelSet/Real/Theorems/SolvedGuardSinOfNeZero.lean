import CORALean.Global.Tensor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# [1, Example 2]'s solved form, away from `x₁ = 0`

Off the line `x₁ = 0`, where `-sin(x₁)/x₁` is defined, `x₂x₁ + sin(x₁) = 0` and
`x₂ = -sin(x₁)/x₁` say the same: [1, Example 2] with the line removed from both sides.
`SolvedGuardSinCounterexample` is the line.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem solvedGuardSin_of_ne_zero :
    {x : Vec ℝ 2 | x 1 * x 0 + Real.sin (x 0) = 0 ∧ x 0 ≠ 0}
      = {x | x 1 = -Real.sin (x 0) / x 0 ∧ x 0 ≠ 0} := by -- --- PROOF ---
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, h0⟩
    refine ⟨?_, h0⟩
    field_simp
    linarith
  · rintro ⟨h, h0⟩
    refine ⟨?_, h0⟩
    rw [h]
    field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
