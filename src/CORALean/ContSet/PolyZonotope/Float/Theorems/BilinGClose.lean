import CORALean.ContSet.PolyZonotope.Float.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

/-!
# A stored `bilin` generator is within its gap of the exact bilinear form

Generator `(i, j)` of the float pairing, rounded down, is off the exact `Gᵢᵀ Q Gⱼ` — read through
`toReal` at the two operands' nominal sets — by at most `bilinGDiff`: the middle vector `Q *ᵥ Gⱼ`
enters as a pair of bounds, picked per term, bracketing the form from both sides.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.bilinG_close (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (i : Fin m) (l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1))) :
    |Real.PolyZonotope.bilinG (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
          (nominal pZ₁) (nominal pZ₂) l i
        - toReal (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l)|
      ≤ toReal (PolyZonotope.bilinGDiff Q pZ₁ pZ₂ i l) := by -- --- PROOF ---
  set l₁ := (finProdFinEquiv.symm l).1 with hl₁
  set l₂ := (finProdFinEquiv.symm l).2 with hl₂
  -- the exact bilinear form, with both vectors read back through `toReal`
  have hexact : Real.PolyZonotope.bilinG (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
        (nominal pZ₁) (nominal pZ₂) l i
      = ∑ r, toReal (PolyZonotope.extG pZ₁ r l₁)
          * ∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ₂ r' l₂) := by
    show (∑ r, Real.PolyZonotope.extG (nominal pZ₁) l₁ r
        * ∑ r', toRealMat (Q i) r r' * Real.PolyZonotope.extG (nominal pZ₂) l₂ r') = _
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [PolyZonotope.toReal_extG pZ₁ r l₁]
    exact congrArg _ (Finset.sum_congr rfl fun r' _ => by
      rw [PolyZonotope.toReal_extG pZ₂ r' l₂]; rfl)
  have hw : ∀ r, toReal (mulVecDown (Q i) (fun r' => PolyZonotope.extG pZ₂ r' l₂) r)
        ≤ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ₂ r' l₂))
      ∧ (∑ r', toReal (Q i r r') * toReal (PolyZonotope.extG pZ₂ r' l₂))
        ≤ toReal (mulVecUp (Q i) (fun r' => PolyZonotope.extG pZ₂ r' l₂) r) :=
    fun r => ⟨dotDown_le (Q i r) _, le_dotUp (Q i r) _⟩
  -- the middle vector enters as a pair of bounds, picked per term, bracketing the bilinear form
  have hlo := PolyZonotope.quadDown_le
    (g := fun r => PolyZonotope.extG pZ₁ r l₁) hw
  have hhi := PolyZonotope.le_quadUp
    (g := fun r => PolyZonotope.extG pZ₁ r l₁) hw
  have hgap := sub_le_subUp (PolyZonotope.bilinGUp Q pZ₁ pZ₂ i l)
    (PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l)
  rw [hexact, abs_le]
  constructor
  · simp only [PolyZonotope.bilinGDiff]
    simp only [PolyZonotope.bilinGDown, PolyZonotope.bilinGUp] at hlo hhi hgap ⊢
    linarith
  · simp only [PolyZonotope.bilinGDiff]
    simp only [PolyZonotope.bilinGDown, PolyZonotope.bilinGUp] at hlo hhi hgap ⊢
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
