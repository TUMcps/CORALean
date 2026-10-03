import CORALean.Global.Tensor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# [1, Example 2]'s solved form drops a line of the guard

[1, Example 2] states that `G = {x | x₂x₁ + sin(x₁) = 0}` equals `{x | x₂ = -sin(x₁)/x₁}`.
On the line `x₁ = 0` the constraint reads `0 = 0`, so all of it is in `G`, while
`-sin(x₁)/x₁` is undefined there — in Lean `0/0 = 0`, which keeps the single point `(0, 0)`.
Either way `(0, 1)` is in `G` and not in the solved form. `SolvedGuardSinOfNeZero` proves the
equality away from `x₁ = 0`, which is what (5) can mean for this `g`.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem solvedGuardSin_counterexample :
    {x : Vec ℝ 2 | x 1 * x 0 + Real.sin (x 0) = 0} ≠
      {x | x 1 = -Real.sin (x 0) / x 0} := by -- --- PROOF ---
  intro h
  have hmem : (![0, 1] : Vec ℝ 2) ∈ {x : Vec ℝ 2 | x 1 * x 0 + Real.sin (x 0) = 0} := by
    simp
  rw [h] at hmem
  simp at hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
