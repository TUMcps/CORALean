module

public import CORALean.ContSet.Zonotope.Real.Operations.CartProd
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.cartProdCost`

Asserted, not proved: `Operations/CartProd.lean` builds the product's center, `n₁ + n₂` entries,
and its generator matrix, `n₁ + n₂` rows by `h₁ + h₂` columns, each operand's generators padded
with zeros in the other component. Nothing is computed, but every entry is a fresh scalar of the
result, and under `Global/Cost.lean`'s model a scalar of the result costs one write, a zero
included.

## Inputs
* `n₁` – first dimension
* `n₂` – second dimension
* `h₁` – first generator count
* `h₂` – second generator count

## Output
* one write per entry of the new matrices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.cartProd` costs at `Vec ℝ n₁` and `Vec ℝ n₂` with `h₁` and `h₂` generators: one
write for each of the `(n₁ + n₂) * (1 + h₁ + h₂)` entries of the new center and generator
matrix. -/
def Zonotope.cartProdCost (n₁ n₂ h₁ h₂ : ℕ) : Cost := ⟨(n₁ + n₂) * (1 + h₁ + h₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
