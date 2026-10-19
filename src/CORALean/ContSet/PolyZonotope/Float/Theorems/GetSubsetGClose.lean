module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDiff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetCoefMem
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# What a rounded `getSubset` generator costs

The exact generator entry is the exact coefficient times the stored generator, and both the
rounded-down and the rounded-up product bracket it, so `getSubsetGDiff` covers the distance to the
stored entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.getSubsetG_close (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋)
    (r : Fin n) (l : Fin (pZ.h * (pZ.maxExp k + 1))) : -- --- CONCL ---
    |Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l r
        - toReal (pZ.getSubsetGDown k cen rad r l)|
      ≤ toReal (pZ.getSubsetGDiff k cen rad r l) := by -- --- PROOF ---
  -- the exact entry is the exact coefficient times the stored generator
  have hexact : Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l r =
      (((pZ.E k (finProdFinEquiv.symm l).1).choose ((finProdFinEquiv.symm l).2 : ℕ) : ℝ)
        * toReal cen ^ (pZ.E k (finProdFinEquiv.symm l).1 - ((finProdFinEquiv.symm l).2 : ℕ))
        * toReal rad ^ ((finProdFinEquiv.symm l).2 : ℕ))
        * toReal (pZ.G (finProdFinEquiv.symm l).1 r) := rfl
  have hc := PolyZonotope.getSubsetCoef_mem pZ k cen rad (finProdFinEquiv.symm l).1
    ((finProdFinEquiv.symm l).2 : ℕ)
  -- the two directed products bracket it
  have hb := Real.Interval.mul_between_corners hc.1 hc.2 (le_refl (toReal (pZ.G
    (finProdFinEquiv.symm l).1 r))) (le_refl (toReal (pZ.G (finProdFinEquiv.symm l).1 r)))
  have hlo := le_trans (Interval.mulLo_le _ _ _ _) hb.1
  have hhi := le_trans hb.2 (Interval.le_mulHi _ _ _ _)
  have hgap := sub_le_subUp (Interval.mulHi (pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1
    ((finProdFinEquiv.symm l).2 : ℕ)).inf (pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1
    ((finProdFinEquiv.symm l).2 : ℕ)).sup (pZ.G (finProdFinEquiv.symm l).1 r)
    (pZ.G (finProdFinEquiv.symm l).1 r)) (pZ.getSubsetGDown k cen rad r l)
  rw [hexact, abs_le]
  simp only [PolyZonotope.getSubsetGDiff, PolyZonotope.getSubsetGDown] at hgap ⊢
  constructor <;> linarith [hlo, hhi, hgap]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
