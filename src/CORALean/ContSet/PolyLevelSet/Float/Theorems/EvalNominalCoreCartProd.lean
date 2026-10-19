module

public import CORALean.ContSet.PolyLevelSet.Float.Theorems.ToRealMatCartProd
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# The stored product's rows, read back

The stored product's values at a point are the exact product's of the two read-back systems: its
coefficients read back as the exact product's (`toRealMat_cartProd`) and the right-hand sides are
stacked.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The product's rows, read back, take the values of the product of the read-back rows. -/
theorem PolyLevelSet.eval_nominalCore_cartProd (P₁ : PolyLevelSet 𝕋 n₁) (P₂ : PolyLevelSet 𝕋 n₂)
    (x : Vec ℝ (n₁ + n₂)) :
    (P₁.cartProd P₂).nominalCore.eval x
      = (P₁.nominalCore.cartProd P₂.nominalCore).eval x := by -- --- PROOF ---
  have hb : toRealVec (P₁.cartProd P₂).b = (P₁.nominalCore.cartProd P₂.nominalCore).b :=
    toRealVec_append _ _
  show toRealMat (P₁.cartProd P₂).A *ᵥ _ - toRealVec (P₁.cartProd P₂).b
    = (P₁.nominalCore.cartProd P₂.nominalCore).A *ᵥ _ - (P₁.nominalCore.cartProd P₂.nominalCore).b
  rw [PolyLevelSet.toRealMat_cartProd, hb]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
