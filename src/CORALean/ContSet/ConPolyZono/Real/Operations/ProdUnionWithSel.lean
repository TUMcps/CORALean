module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionWithSel
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdUnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdAddCol

@[expose] public section

/-!
# The monomial of a column carrying the selector

The selector splits off as a factor of its own, which is what lets the value of
the whole constraint row be read as a polynomial in `α₁` and the two block means.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand
* `a` – factor values
* `c` – exponent column

## Hypotheses
* none

## Conclusion
* the selector multiplies the monomial by the selector factor
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.prod_unionWithSel {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ)
    (c : Fin (p₁ + p₂ + 2) → ℕ) :
    (∏ k, a k ^ ConPolyZono.unionWithSel p₁ p₂ c k)
      = a (ConPolyZono.unionSel p₁ p₂) * ∏ k, a k ^ c k := by
  simp only [ConPolyZono.unionWithSel]
  rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, pow_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
