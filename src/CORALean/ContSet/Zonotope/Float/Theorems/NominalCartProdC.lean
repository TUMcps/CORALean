module

public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.Global.AppendLinear

@[expose] public section

/-!
# The nominal center of `Zonotope.cartProd`

The stored center of the product, read as reals, is the pair of the operands' nominal centers
appended.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Hypotheses
* none

## Conclusion
* nominal center of the product is the appended pair
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

/-- The nominal center of the product is the exact pair, appended. -/
theorem Zonotope.nominal_cartProd_c (Z₁ : Zonotope (Vec 𝕋 n₁))
    (Z₂ : Zonotope (Vec 𝕋 n₂)) : -- --- CONCL ---
    (InflatedContSet.nominal (Z₁.cartProd Z₂)).c =
      appendLinear n₁ n₂
        ((InflatedContSet.nominal Z₁).c, (InflatedContSet.nominal Z₂).c) := by -- --- PROOF ---
  rw [appendLinear_apply]
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · show toReal (Fin.append Z₁.c Z₂.c (Fin.castAdd n₂ i)) = Fin.append
      (InflatedContSet.nominal Z₁).c (InflatedContSet.nominal Z₂).c (Fin.castAdd n₂ i)
    rw [Fin.append_left, Fin.append_left]
    rfl
  · show toReal (Fin.append Z₁.c Z₂.c (Fin.natAdd n₁ i)) = Fin.append
      (InflatedContSet.nominal Z₁).c (InflatedContSet.nominal Z₂).c (Fin.natAdd n₁ i)
    rw [Fin.append_right, Fin.append_right]
    rfl


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
