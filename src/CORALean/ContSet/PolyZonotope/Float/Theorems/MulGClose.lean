module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
public import CORALean.ContSet.PolyZonotope.Real.Operations.MulGApply

@[expose] public section

/-!
# A stored product generator is close to the exact one

Shared by `MulOuter` and `EvalPolyOuter`, which both need it and cannot import
one another: `mul_outer` prices one call, `evalPoly_outer`'s recursion one call
per Horner step. `mulDown`/`mulUp` bracket the exact product directly, and
`subUp` covers the gap between them.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `i` – coordinate
* `l` – generator index

## Hypotheses
* none

## Conclusion
* stored generator is within its gap of the exact product
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What a rounded product generator costs. -/
theorem PolyZonotope.mulG_close (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1))) : -- --- CONCL ---
    |Real.PolyZonotope.mulG (nominal pZ₁) (nominal pZ₂) l i
        - toReal (PolyZonotope.mulGDown pZ₁ pZ₂ i l)|
      ≤ toReal (PolyZonotope.mulGDiff pZ₁ pZ₂ i l) := by -- --- PROOF ---
  have hexact : Real.PolyZonotope.mulG (nominal pZ₁) (nominal pZ₂) l i
      = toReal (PolyZonotope.extG pZ₁ i (finProdFinEquiv.symm l).1)
        * toReal (PolyZonotope.extG pZ₂ i (finProdFinEquiv.symm l).2) := by
    simp only [Real.PolyZonotope.mulG_apply, PolyZonotope.toReal_extG]
  -- the two directed products bracket the exact one, and `subUp` covers the gap
  have hlo := mulDown_le_mul (PolyZonotope.extG pZ₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG pZ₂ i (finProdFinEquiv.symm l).2)
  have hhi := mul_le_mulUp (PolyZonotope.extG pZ₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG pZ₂ i (finProdFinEquiv.symm l).2)
  have hgap := sub_le_subUp (PolyZonotope.mulGUp pZ₁ pZ₂ i l) (PolyZonotope.mulGDown pZ₁ pZ₂ i l)
  rw [hexact, abs_le]
  simp only [PolyZonotope.mulGDiff, PolyZonotope.mulGDown, PolyZonotope.mulGUp] at hlo hhi hgap ⊢
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
