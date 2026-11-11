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
# A zonotope made independent holds its points in its fiber

A zonotope made independent has no factors, and every one of its points is in its one fiber.

## Inputs
* `Z` – zonotope
* `y` – point
* `b` – factor values (none)

## Hypotheses
* `hy` – the point is in the zonotope

## Conclusion
* the point is in the fiber of the independent form
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

/-- A point of a zonotope is in the fiber of its independent form, which has no factors. -/
theorem Zonotope.mem_fiber_ofIndep (Z : Zonotope (Vec 𝕋 n)) {y : Vec ℝ n} (hy : y ∈ Z.toSet)
    (b : Fin Z.ofIndep.p → ℝ) : -- --- CONCL ---
    y ∈ Z.ofIndep.fiber b := by -- --- PROOF ---
  obtain ⟨y', hy', e, he, rfl⟩ := hy
  obtain ⟨β, hβ, hyβ⟩ := Zonotope.mem_nominalSet_iff.mp hy'
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β, hβ, e, he, ?_⟩
  funext i
  repeat rw [PolyZonotope.nominal_point_eq]
  simp only [Pi.add_apply, hyβ i]
  have h0 : ∑ l : Fin Z.ofIndep.h, toReal (Z.ofIndep.G l i)
      * Real.PolyZonotope.monomial Z.ofIndep.E b l = 0 :=
    Finset.sum_eq_zero fun l _ => Fin.elim0 l
  rw [h0]
  show _ = toReal (Z.c i) + 0 + _ + e i
  rw [add_zero]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
