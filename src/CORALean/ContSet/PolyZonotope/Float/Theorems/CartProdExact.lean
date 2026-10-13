import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalSetCartProd
import CORALean.ContSet.InflatedContSet.Theorems.AppendConstruct

/-!
# `PolyZonotope.cartProd` is exact

The stored operands' sets, paired and read through `Fin.append`, are the product's set. Nothing
rounds: the nominal part is the exact layer's `cartProd` mapped through the append, field by
field, and the error box is the stack of the two.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cartProd_exact (pZ₁ : PolyZonotope (Vec 𝕋 n₁))
    (pZ₂ : PolyZonotope (Vec 𝕋 n₂)) :
    (pZ₁.cartProd pZ₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (pZ₁.construct ×ˢ pZ₂.construct) := by
  -- the nominal part: the exact product, mapped through the append
  have hN := PolyZonotope.nominalSet_cartProd pZ₁ pZ₂
  -- the error box is the stack of the two, and stacking distributes over the sum
  exact CORALean.Float.InflatedContSet.append_construct (s₁ := pZ₁) (s₂ := pZ₂) hN rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
