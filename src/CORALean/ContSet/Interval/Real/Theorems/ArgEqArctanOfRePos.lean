module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# The argument in the right half-plane is an arctangent

For `0 < re z` the argument lies in `(-π/2, π/2)` and has tangent `im z / re z`, so it is
`arctan (im z / re z)`. This is `atan2 y x = arctan (y / x)` for `x > 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [← Complex.tan_arg, Real.arctan_tan (abs_lt.mp h2).1 (abs_lt.mp h2).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
