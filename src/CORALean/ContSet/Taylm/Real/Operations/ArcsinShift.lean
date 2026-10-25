module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# `Taylm.arcsinShift`

The `g(x) = f(x)·√(1 - c_f²) - c_f·√(1 - f(x)²)` of [1, Def. 3 (arcsin)], at a value `a` of
`f` and its center `c`: the argument the source's addition formula hands to `arcsin`, so that
the expansion is taken about `0` rather than about `c_f`.

## Inputs
* `c` – center
* `a` – point to shift

## Output
* shifted argument of the arcsine addition formula

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


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.arcsinShift (c a : ℝ) : ℝ :=
  a * Real.sqrt (1 - c ^ 2) - c * Real.sqrt (1 - a ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
