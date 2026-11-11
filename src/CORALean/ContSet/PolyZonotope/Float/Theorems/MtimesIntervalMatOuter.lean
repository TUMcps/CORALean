module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesIntervalMatFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter

@[expose] public section

/-!
# An interval matrix times a polynomial zonotope holds every product

The result holds the product of every matrix of the box and every point of the set.

## Inputs
* `IM` – interval matrix
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the images of the set under the matrices of the box are a subset of the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result holds the product of every matrix of the box and every point of the set. -/
theorem PolyZonotope.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n))
    (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (⋃ M ∈ IM.toSet, (M *ᵥ ·) '' pZ.toSet) ⊆
      (PolyZonotope.mtimesIntervalMat IM pZ).toSet := by -- --- PROOF ---
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨M, hM, x, hx, rfl⟩ := hy
  obtain ⟨a, ha, hxa⟩ := (PolyZonotope.mem_toSet_iff_fiber pZ x).mp hx
  exact (PolyZonotope.mem_toSet_iff_fiber _ _).mpr
    ⟨a, ha, PolyZonotope.mtimesIntervalMat_fiber IM pZ hM ha hxa⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
