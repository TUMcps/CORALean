module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Eq. (54): the interpolated gain

`interpGain`: [1]'s `φ(j+1)` of eq. (54), the gain interpolated between `φ⁽¹⁾` at
the horizon and the limit gain `ζ_δ`.

## Inputs
* `ζδ` – limit gain
* `φ1` – gain at the horizon
* `j` – interpolation index

## Output
* the interpolated gain

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ(j+1)` of eq. (54): the gain interpolated between `φ⁽¹⁾` at the horizon
and the limit gain `ζ_δ`. -/
noncomputable def interpGain (ζδ φ1 : ℝ) (j : ℕ) : ℝ :=
  ζδ + (φ1 - ζδ) * ζδ ^ j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
