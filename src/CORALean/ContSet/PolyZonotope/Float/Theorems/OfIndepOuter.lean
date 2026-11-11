module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A zonotope made independent holds the zonotope

The set of `ofIndep` contains the set of the zonotope.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the zonotope is a subset of the set of its independent form
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

/-- A zonotope made independent holds the zonotope. -/
theorem Zonotope.ofIndep_outer (Z : Zonotope (Vec 𝕋 n)) : Z.toSet ⊆ Z.ofIndep.toSet := fun y hy =>
  (PolyZonotope.mem_toSet_iff_fiber _ y).mpr ⟨Fin.elim0, fun k => Fin.elim0 k,
    Zonotope.mem_fiber_ofIndep Z hy _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
