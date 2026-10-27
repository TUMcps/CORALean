module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The area of an approximation in the input-output plane

[1, Eq. 10]: `area([e, ē], [l, u]) = (u - l)(ē - e)`, the integrated approximation error over
`[l, u]` that [1, Prop. 11] compares across enclosures.

## Inputs
* `e` – lower error
* `e'` – upper error
* `l` – lower end of the interval
* `u` – upper end of the interval

## Output
* area of the error band over the interval

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(u - l)(ē - e)`, the area of the band `[e, ē]` over `[l, u]`. -/
def approxArea (e e' l u : ℝ) : ℝ := (u - l) * (e' - e)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
