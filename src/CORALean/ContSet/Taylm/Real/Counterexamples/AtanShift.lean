module

public import CORALean.ContSet.Taylm.Real.Operations.AtanShift
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# The arctangent addition formula fails without `1 + c_f·f > 0`

[1, Def. 3 (arctan)] states its rewriting for every model. At `c_f = √3` and a value
`f(x) = -√3`, `1 + c_f·f = -2` and `g = √3`, so the right side is `π/3 + π/3` where the left is
`-π/3`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the arctangent addition formula fails for some points

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.atanShift_counterexample : -- --- CONCL ---
    ∃ a c : ℝ, Real.arctan a ≠
      Real.arctan c + Real.arctan (Taylm.atanShift c a) := by -- --- PROOF ---
  refine ⟨-Real.sqrt 3, Real.sqrt 3, fun h => ?_⟩
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  -- `g = (-2√3) / (-2) = √3`
  have hg : Taylm.atanShift (Real.sqrt 3) (-Real.sqrt 3) = Real.sqrt 3 := by
    rw [Taylm.atanShift, show 1 + Real.sqrt 3 * -Real.sqrt 3 = -2 by linarith]
    ring
  rw [hg, Real.arctan_neg, Real.arctan_sqrt_three] at h
  linarith [Real.pi_pos]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
