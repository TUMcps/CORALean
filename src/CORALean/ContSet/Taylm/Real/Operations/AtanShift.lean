import Mathlib.Data.Real.Basic

/-!
# `Taylm.atanShift`

The `g(x) = (f(x) - c_f) / (1 + c_f·f(x))` of [1, Def. 3 (arctan)], at a value `a` of `f` and its
centre `c`: the argument the source's addition formula hands to `arctan`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.atanShift (c a : ℝ) : ℝ := (a - c) / (1 + c * a)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
