module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionSelRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConRow
public import CORALean.ContSet.PolyLevelSet.Float.Operations.And

@[expose] public section

/-!
# `ConPolyZono.unionUpper` over a floating-point scalar

`Real.ConPolyZono.unionUpper` at the stored floats: the two selector rows of [1, Thm. 1] stacked
by `PolyLevelSet.and_`, `α₁α₂ = 1` stored exactly and the selector polynomial with its
coefficients' rounding as its slack.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector rows, both equations. -/
def ConPolyZono.unionUpper (p₁ p₂ : ℕ) : PolyLevelSet 𝕋 (p₁ + p₂ + 2) :=
  (ConPolyZono.unionSelRow p₁ p₂).and_ (ConPolyZono.unionConRow p₁ p₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
