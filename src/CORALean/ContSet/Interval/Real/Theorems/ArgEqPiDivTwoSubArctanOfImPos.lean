import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The argument in the upper half-plane is a shifted arctangent
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `0 < im z`: `arg z = π/2 - arctan (re z / im z)`, the cotangent form of `atan2 y x` for
`y > 0`. The argument lies in `(0, π)`, where `π/2 - arg z` has tangent `re z / im z`. -/
theorem arg_eq_pi_div_two_sub_arctan_of_im_pos {z : ℂ} (h : 0 < z.im) :
    Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by -- --- PROOF ---
  have h0 : 0 < Complex.arg z :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) fun e => by
      rw [eq_comm, Complex.arg_eq_zero_iff] at e; exact absurd e.2 h.ne'
  have h1 : Complex.arg z < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi z) fun e => by
      rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 h.ne'
  have ht : Real.tan (Real.pi / 2 - Complex.arg z) = z.re / z.im := by
    rw [Real.tan_pi_div_two_sub, Complex.tan_arg, inv_div]
  have := Real.arctan_tan (x := Real.pi / 2 - Complex.arg z) (by linarith) (by linarith)
  rw [ht] at this
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
