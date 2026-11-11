module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# Materialising keeps the fiber

`materialise` changes the stored form of a polynomial zonotope and nothing a fiber can see.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the fibers of `pZ` and `pZ.materialise` at `a` are equal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `materialise` changes nothing the fiber can see. -/
theorem PolyZonotope.fiber_materialise (pZ : PolyZonotope (Vec 𝕋 n))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    pZ.materialise.fiber a = pZ.fiber a := by -- --- PROOF ---
  have hdep : pZ.materialise.nominal.point a = pZ.nominal.point a := by
    funext i
    repeat rw [PolyZonotope.nominal_point_eq]
    simp [PolyZonotope.materialise]
    rfl
  have hind : ∀ β : Fin pZ.q → ℝ, (fun i => ∑ j : Fin pZ.materialise.q,
      toReal (pZ.materialise.GI j i) * β j) = fun i => ∑ j, toReal (pZ.GI j i) * β j := by
    intro β
    funext i
    simp [PolyZonotope.materialise]
    rfl
  have hI : pZ.materialise.I_error = pZ.I_error := by
    simp [PolyZonotope.materialise]
  ext x
  rw [PolyZonotope.mem_fiber_iff, PolyZonotope.mem_fiber_iff]
  simp only [hdep, hind, hI]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
