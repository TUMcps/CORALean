import CORALean.ContSet.Taylm.Real.Operations.ArcsinShift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# When the arcsine addition formula holds

[1, Def. 3 (arcsin)] rewrites `arcsin f = arcsin c_f + arcsin g` under the sole condition that
the range lies in `(-1, 1)`. `g` is `sin (arcsin f - arcsin c_f)`, so the identity is
`arcsin (sin θ) = θ`, which holds exactly when `|θ| ≤ π/2`: the corrected condition, and the
reason the printed one is not enough (`ArcsinShiftCounterexample`).

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {a c : ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.arcsin_eq_add_arcsinShift_iff (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    Real.arcsin a = Real.arcsin c + Real.arcsin (Taylm.arcsinShift c a)
      ↔ |Real.arcsin a - Real.arcsin c| ≤ Real.pi / 2 := by -- --- PROOF ---
  -- `g` is the sine of the difference of the two angles
  have hg : Taylm.arcsinShift c a = Real.sin (Real.arcsin a - Real.arcsin c) := by
    rw [Real.sin_sub, Real.sin_arcsin' ha, Real.sin_arcsin' hc, Real.cos_arcsin,
      Real.cos_arcsin, Taylm.arcsinShift]
    ring
  rw [hg, abs_le]
  constructor
  · intro h
    have h₁ := Real.neg_pi_div_two_le_arcsin (Real.sin (Real.arcsin a - Real.arcsin c))
    have h₂ := Real.arcsin_le_pi_div_two (Real.sin (Real.arcsin a - Real.arcsin c))
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    rw [Real.arcsin_sin h₁ h₂]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
