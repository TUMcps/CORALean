import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `Taylm.arcsinShift`

The `g(x) = f(x)·√(1 - c_f²) - c_f·√(1 - f(x)²)` of [1, Def. 3 (arcsin)], at a value `a` of
`f` and its centre `c`: the argument the source's addition formula hands to `arcsin`, so that
the expansion is taken about `0` rather than about `c_f`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.arcsinShift (c a : ℝ) : ℝ :=
  a * Real.sqrt (1 - c ^ 2) - c * Real.sqrt (1 - a ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
