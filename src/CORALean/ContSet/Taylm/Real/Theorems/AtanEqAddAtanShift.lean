import CORALean.ContSet.Taylm.Real.Operations.AtanShift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# When the arctangent addition formula holds

[1, Def. 3 (arctan)] rewrites `arctan f = arctan c_f + arctan g` with no condition at all. It is
`arctan_add` at `f` and `-c_f`, which needs `f·(-c_f) < 1`: the corrected condition is
`1 + c_f·f > 0` on the domain, without which the formula fails (`AtanShiftCounterexample`).

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

theorem Taylm.arctan_eq_add_atanShift (h : 0 < 1 + c * a) :
    Real.arctan a = Real.arctan c + Real.arctan (Taylm.atanShift c a) := by -- --- PROOF ---
  have hadd := Real.arctan_add (x := a) (y := -c) (by linarith)
  rw [Real.arctan_neg] at hadd
  rw [Taylm.atanShift, show a - c = a + -c by ring, show 1 + c * a = 1 - a * -c by ring,
    ← hadd]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
