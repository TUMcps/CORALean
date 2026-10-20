module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# Columns add where monomials multiply

`PolyZonotope.monomial_add` read at a single column rather than at a whole
matrix, which is the form an assembled column is in.

## Inputs
* `p` – number of factors
* `a` – factor values
* `c` – first exponent column
* `d` – second exponent column

## Hypotheses
* none

## Conclusion
* the monomial of the summed columns is the product of the two monomials
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.prod_addCol {p : ℕ} (a : Fin p → ℝ) (c d : Fin p → ℕ) :
    (∏ k, a k ^ (c k + d k)) = (∏ k, a k ^ c k) * ∏ k, a k ^ d k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add (a k) (c k) (d k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
