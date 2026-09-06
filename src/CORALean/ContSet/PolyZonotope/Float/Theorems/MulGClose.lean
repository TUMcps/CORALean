import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG

/-!
# A stored product generator is close to the exact one

Shared by `MulOuter` and `EvalPolyOuter`, which both need it and cannot import
one another: `mul_outer` prices one call, `evalPoly_outer`'s recursion one call
per Horner step. `mulDown`/`mulUp` bracket the exact product directly, and
`subUp` covers the gap between them.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What a rounded product generator costs. -/
theorem PolyZonotope.mulG_close (S₁ S₂ : PolyZonotope 𝕋 n) (i : Fin n)
    (l : Fin ((S₁.h + 1) * (S₂.h + 1))) :
    |Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
        - toReal (PolyZonotope.mulGDown S₁ S₂ i l)|
      ≤ toReal (PolyZonotope.mulGDiff S₁ S₂ i l) := by
  have hexact : Real.PolyZonotope.mulG (nominal S₁) (nominal S₂) l i
      = toReal (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
        * toReal (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2) := by
    simp only [Real.PolyZonotope.mulG, PolyZonotope.toReal_extG]
  -- the two directed products bracket the exact one, and `subUp` covers the gap
  have hlo := mulDown_le_mul (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)
  have hhi := mul_le_mulUp (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)
  have hgap := sub_le_subUp (PolyZonotope.mulGUp S₁ S₂ i l) (PolyZonotope.mulGDown S₁ S₂ i l)
  rw [hexact, abs_le]
  simp only [PolyZonotope.mulGDiff, PolyZonotope.mulGDown, PolyZonotope.mulGUp] at hlo hhi hgap ⊢
  constructor <;> linarith

end CORALean.Float
