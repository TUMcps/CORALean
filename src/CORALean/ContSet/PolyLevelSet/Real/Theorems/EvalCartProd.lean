module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The rows of `PolyLevelSet.cartProd`

The product's values at a point are each operand's at its own block of variables: a row of either
operand reads exponent zero on the other's variables and has coefficient zero on its monomials.

## Inputs
* `P₁` – first level set
* `P₂` – second level set
* `x` – point

## Hypotheses
* none

## Conclusion
* the product's values are each operand's at its own variables
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both operands' constraint values, each at its own variables, stacked. -/
theorem PolyLevelSet.eval_cartProd (P₁ : PolyLevelSet n₁) (P₂ : PolyLevelSet n₂)
    (x : Vec ℝ (n₁ + n₂)) :
    (P₁.cartProd P₂).eval x = Fin.append (P₁.eval fun k => x (Fin.castAdd n₂ k))
      (P₂.eval fun k => x (Fin.natAdd n₁ k)) := by -- --- PROOF ---
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
  · show ((P₁.cartProd P₂).A *ᵥ PolyZonotope.monomial (P₁.cartProd P₂).R x) (Fin.castAdd P₂.m i)
        - Fin.append P₁.b P₂.b (Fin.castAdd P₂.m i) = Fin.append _ _ (Fin.castAdd P₂.m i)
    simp only [PolyLevelSet.cartProd, PolyLevelSet.eval, Matrix.mulVec, dotProduct, Pi.sub_apply,
      Fin.append_left, sub_left_inj]
    exact (Fin.sum_univ_add _).trans (by simp [PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right])
  · show ((P₁.cartProd P₂).A *ᵥ PolyZonotope.monomial (P₁.cartProd P₂).R x) (Fin.natAdd P₁.m i)
        - Fin.append P₁.b P₂.b (Fin.natAdd P₁.m i) = Fin.append _ _ (Fin.natAdd P₁.m i)
    simp only [PolyLevelSet.cartProd, PolyLevelSet.eval, Matrix.mulVec, dotProduct, Pi.sub_apply,
      Fin.append_right, sub_left_inj]
    exact (Fin.sum_univ_add _).trans (by simp [PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
