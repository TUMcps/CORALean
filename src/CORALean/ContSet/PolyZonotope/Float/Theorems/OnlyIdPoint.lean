module

public import CORALean.ContSet.PolyZonotope.Float.Operations.OnlyId
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OnlyIdPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `PolyZonotope.onlyId` splits the nominal point, in float too

The nominal parts of the two results are the exact layer's `onlyId` of the original's nominal part
(`aux_onlyId_nominal_G`; `zero` reads as `0`, nothing rounds), so the point of the original at a
factor vector is the sum of the first part's point at the factors of `S` and the second's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator matrices of both parts are the exact layer's. -/
theorem PolyZonotope.aux_onlyId_nominal_G (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    (nominal (pZ.onlyId S).1).G = (Real.PolyZonotope.onlyId (nominal pZ) S).1.G ∧
      (nominal (pZ.onlyId S).2).G =
        (Real.PolyZonotope.onlyId (nominal pZ) S).2.G := by -- --- PROOF ---
  constructor
  · funext l i
    simp only [Real.PolyZonotope.onlyId, PolyZonotope.onlyId, nominal]
    split_ifs <;> simp [toReal_zero, RealImage.realImage, toRealVec]
  · funext l i
    simp only [Real.PolyZonotope.onlyId, PolyZonotope.onlyId, nominal]
    split_ifs <;> simp [toReal_zero, RealImage.realImage, toRealVec]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact at the nominal points. -/
theorem PolyZonotope.onlyId_point (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p))
    (a : Fin pZ.p → ℝ) : -- --- STMT ---
    (nominal pZ).point a
      = (nominal (pZ.onlyId S).1).point (fun k' : Fin S.card => a (S.orderIsoOfFin rfl k').1)
        + (nominal (pZ.onlyId S).2).point a := by -- --- PROOF ---
  have key := Real.PolyZonotope.onlyId_point (nominal pZ) S a
  have hG := PolyZonotope.aux_onlyId_nominal_G pZ S
  rw [key]
  congr 1
  · unfold Real.PolyZonotope.point
    rw [hG.1]
    rfl
  · have hc : (nominal (pZ.onlyId S).2).c = (Real.PolyZonotope.onlyId (nominal pZ) S).2.c :=
      funext fun _ => toReal_zero
    unfold Real.PolyZonotope.point
    rw [hG.2, hc]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
