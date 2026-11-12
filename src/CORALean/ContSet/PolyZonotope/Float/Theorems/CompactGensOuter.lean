module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber

@[expose] public section

/-!
# `compactGens` over-approximates, merging generator columns

The set is the union of its fibers at the factor values of the unit box, and `compactGens` keeps
each fiber (`compactGens_fiber`).

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactGens_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.toSet ⊆ pZ.compactGens.toSet := fun x hx => by
  obtain ⟨a, ha, hxa⟩ := (PolyZonotope.mem_toSet_iff_fiber pZ x).mp hx
  exact (PolyZonotope.mem_toSet_iff_fiber _ x).mpr ⟨a, ha, PolyZonotope.compactGens_fiber pZ ha hxa⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
