import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.representsa_point`

CORA's `@conPolyZono/representsa_` at type `point` [1]: `isempty(cPZ.G) && isempty(cPZ.GI)`, no
dependent and no independent generator column. The constraints are not read.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono/representsa_` at `point`: no generator column of either block. -/
def ConPolyZono.representsa_point (cPZ : ConPolyZono α) : Bool := cPZ.h == 0 && cPZ.q == 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
