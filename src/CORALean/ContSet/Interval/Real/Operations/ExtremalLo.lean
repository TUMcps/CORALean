module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Interval.extremalLo`

[1, Sec. 3 (extremal bounds)]: for `g[Y](x) = Σᵢ [cᵢ] hᵢ(x)`, the lower extremal function
`g̲[Y](x) = Σᵢ cᵢ⁻(x) hᵢ(x)`, each coefficient read off `[cᵢ]` at the bound the sign of `hᵢ(x)`
selects: the lower one where `hᵢ(x) ≥ 0`, the upper one where `hᵢ(x) ≤ 0`. The coefficient box
is `C` and `h` the vector of values `hᵢ(x)` at one `x`, every index summed, the constant
term included: the paper sums from `i = 1` while its `g[Y]` and its example start at `i = 0`.

## Inputs
* `C` – box of coefficients
* `h` – weight vector

## Output
* smallest value of `h` against the box

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor Based
      on Extremal Functions". Principles and Practice of Constraint Programming – CP 2010, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g̲[Y](x)` at the values `h = (hᵢ(x))ᵢ` and the coefficient box `C = ([cᵢ])ᵢ`. -/
noncomputable def Interval.extremalLo (C : Interval (Vec ℝ m)) (h : Vec ℝ m) : ℝ :=
  ∑ i, (if 0 ≤ h i then C.inf i else C.sup i) * h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
