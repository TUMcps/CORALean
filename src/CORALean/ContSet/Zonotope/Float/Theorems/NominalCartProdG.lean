import CORALean.ContSet.Zonotope.Float.Operations.CartProd
import CORALean.ContSet.Zonotope.Real.Operations.CartProd
import CORALean.Global.AppendLinear

/-!
# The nominal generators of `Zonotope.cartProd`

Column by column, the stored generators of the product, read as reals, are the exact layer's
block-diagonal columns appended.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_realG_left (Z₁ : Zonotope (Vec 𝕋 n₁)) (Z₂ : Zonotope (Vec 𝕋 n₂))
    (j : Fin Z₁.h) :
    (Real.Zonotope.cartProd (InflatedContSet.nominal Z₁) (InflatedContSet.nominal Z₂)).G
      (Fin.castAdd Z₂.h j) = ((InflatedContSet.nominal Z₁).G j, 0) := by
  dsimp only [Real.Zonotope.cartProd]
  exact Fin.append_left (m := Z₁.h) (n := Z₂.h) _ _ j

theorem Zonotope.aux_realG_right (Z₁ : Zonotope (Vec 𝕋 n₁)) (Z₂ : Zonotope (Vec 𝕋 n₂))
    (j : Fin Z₂.h) :
    (Real.Zonotope.cartProd (InflatedContSet.nominal Z₁) (InflatedContSet.nominal Z₂)).G
      (Fin.natAdd Z₁.h j) = (0, (InflatedContSet.nominal Z₂).G j) := by
  dsimp only [Real.Zonotope.cartProd]
  exact Fin.append_right (m := Z₁.h) (n := Z₂.h) _ _ j


-- =======================================  MAIN THEOREM  ======================================= --

/-- The nominal generators of the product are the exact block-diagonal ones, appended. -/
theorem Zonotope.nominal_cartProd_G (Z₁ : Zonotope (Vec 𝕋 n₁)) (Z₂ : Zonotope (Vec 𝕋 n₂))
    (j : Fin (Z₁.h + Z₂.h)) :
    (InflatedContSet.nominal (Z₁.cartProd Z₂)).G j = appendLinear n₁ n₂
      ((Real.Zonotope.cartProd (InflatedContSet.nominal Z₁)
        (InflatedContSet.nominal Z₂)).G j) := by -- --- PROOF ---
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Zonotope.aux_realG_left, appendLinear_apply]
    exact toReal_genBlockDiag_left (fun i j => Z₁.G j i) (fun i j => Z₂.G j i) j
  · rw [Zonotope.aux_realG_right, appendLinear_apply]
    exact toReal_genBlockDiag_right (fun i j => Z₁.G j i) (fun i j => Z₂.G j i) j


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
