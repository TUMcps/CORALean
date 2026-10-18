module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConErr

@[expose] public section

/-!
# `ConPolyZono.unionUpperB`

What the two selector rows of [1, Thm. 1] are held to: `α₁α₂ = 1` exactly, and the scaled selector
polynomial `0`, within the slack `unionConErr` that `union` records, the rounding of its integer
coefficients.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand sides of the two selector rows. -/
def ConPolyZono.unionUpperB : Vec 𝕋 (1 + 1) :=
  ConPolyZono.plusB (fun _ => one) (fun _ => zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
