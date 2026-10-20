module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqPiDivTwoSubArctanOfImPos

@[expose] public section

/-!
# The argument in the lower half-plane is a shifted arctangent

## Inputs
* `z` – complex number

## Hypotheses
* `h` – imaginary part negative

## Conclusion
* the argument is minus a quarter turn minus an arctangent
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `im z < 0`: `arg z = -(π/2) - arctan (re z / im z)`, the mirror image of the upper
half-plane form under conjugation. -/
theorem arg_eq_neg_pi_div_two_sub_arctan_of_im_neg {z : ℂ} (h : z.im < 0) :
    Complex.arg z = -(Real.pi / 2) - Real.arctan (z.re / z.im) := by -- --- PROOF ---
  have hne : Complex.arg z ≠ Real.pi := fun e => by
    rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 h.ne
  have hc := Complex.arg_conj z
  rw [if_neg hne, arg_eq_pi_div_two_sub_arctan_of_im_pos (z := (starRingEnd ℂ) z)
    (by simpa using h)] at hc
  simp only [Complex.conj_re, Complex.conj_im, div_neg, Real.arctan_neg] at hc
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
