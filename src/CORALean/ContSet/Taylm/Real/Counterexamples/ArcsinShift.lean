module

public import CORALean.ContSet.Taylm.Real.Theorems.ArcsinEqAddArcsinShiftIff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The arcsine addition formula fails inside `(-1, 1)`

[1, Def. 3 (arcsin)] asks only that the range lie in `(-1, 1)`. At `c_f = -√3/2` and a value
`f(x) = √3/2` the angles are `∓π/3`, two thirds of `π` apart: `g = √3/2` again, and the right
side is `-π/3 + π/3 = 0` where the left is `π/3`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the arcsine addition formula fails for some points in the open unit interval

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.arcsinShift_counterexample :
    ∃ a ∈ Set.Ioo (-1 : ℝ) 1, ∃ c ∈ Set.Ioo (-1 : ℝ) 1,
      Real.arcsin a ≠ Real.arcsin c + Real.arcsin (Taylm.arcsinShift c a) := by -- --- PROOF ---
  have hs : Real.sin (Real.pi / 3) < 1 := by
    rw [Real.sin_pi_div_three]
    have : Real.sqrt 3 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hs0 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  refine ⟨Real.sin (Real.pi / 3), ⟨by linarith, hs⟩, -Real.sin (Real.pi / 3),
    ⟨by linarith, by linarith⟩, fun h => ?_⟩
  -- the identity would put the two angles at most `π/2` apart
  have hiff := (Taylm.arcsin_eq_add_arcsinShift_iff (a := Real.sin (Real.pi / 3))
    (c := -Real.sin (Real.pi / 3)) ⟨by linarith, hs.le⟩ ⟨by linarith, by linarith⟩).1 h
  rw [Real.arcsin_neg, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    sub_neg_eq_add, abs_of_pos (by linarith [Real.pi_pos])] at hiff
  linarith [Real.pi_pos]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
