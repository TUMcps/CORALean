module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# [1, Example 2]'s solved form drops a line of the guard

[1, Example 2] states that `G = {x | x₂x₁ + sin(x₁) = 0}` equals `{x | x₂ = -sin(x₁)/x₁}`.
On the line `x₁ = 0` the constraint reads `0 = 0`, so all of it is in `G`, while
`-sin(x₁)/x₁` is undefined there — in Lean `0/0 = 0`, which keeps the single point `(0, 0)`.
Either way `(0, 1)` is in `G` and not in the solved form. `SolvedGuardSinOfNeZero` proves the
equality away from `x₁ = 0`, which is what (5) can mean for this `g`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the solved form drops a line of the guard set

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem solvedGuardSin_counterexample : -- --- CONCL ---
    {x : Vec ℝ 2 | x 1 * x 0 + Real.sin (x 0) = 0} ≠
      {x | x 1 = -Real.sin (x 0) / x 0} := by -- --- PROOF ---
  intro h
  have hmem : (![0, 1] : Vec ℝ 2) ∈ {x : Vec ℝ 2 | x 1 * x 0 + Real.sin (x 0) = 0} := by
    simp
  rw [h] at hmem
  simp at hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
