module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd

@[expose] public section

/-!
# The stored product's coefficients, read back

The product's coefficient matrix reads back as the exact product's of the read-back operands: the
off-blocks are `zero`, which reads as `0`, and every other entry is copied.

## Inputs
* `P₁` – first level set
* `P₂` – second level set

## Hypotheses
* none

## Conclusion
* the product's coefficients read back as the exact product's
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The product's coefficients, read back, are the product of the read-back ones. -/
theorem PolyLevelSet.toRealMat_cartProd (P₁ : PolyLevelSet 𝕋 n₁) (P₂ : PolyLevelSet 𝕋 n₂) :
    toRealMat (P₁.cartProd P₂).A = (P₁.nominalCore.cartProd P₂.nominalCore).A := by
  funext i l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
    simp [toRealMat, PolyLevelSet.cartProd, Real.PolyLevelSet.cartProd, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
