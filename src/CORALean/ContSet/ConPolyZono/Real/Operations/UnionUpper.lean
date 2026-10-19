module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSelRow
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConRow
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.unionUpper`

The two selector rows of [1, Thm. 1], the upper half of its constraint, stacked over the union's
factors by `PolyLevelSet.andRows`: `α₁α₂ = 1` (`unionSelRow`) and the selector polynomial `= 0`
(`unionConRow`). Block-diagonal, since neither row reads the other's monomials.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector rows, both equations, on the unit box. -/
noncomputable def ConPolyZono.unionUpper (p₁ p₂ : ℕ) : PolyLevelSet (p₁ + p₂ + 2) :=
  (ConPolyZono.unionSelRow p₁ p₂).andRows (ConPolyZono.unionConRow p₁ p₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
