module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.PartZonotopeNominal

@[expose] public section

/-!
# `partZonotope` encloses the original, in float too

The nominal part of the float `partZonotope` is the exact layer's (`partZonotope_nominal`) and the
error box is copied, so the exact layer's enclosure carries over. Not exact: different patterns
get independent factors, so the inclusion is strict in general.

## Inputs
* `pZ` – polynomial zonotope
* `V` – selected factors

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.partZonotope_outer (pZ : PolyZonotope (Vec 𝕋 n)) (V : Finset (Fin pZ.p)) :
    pZ.construct ⊆ (pZ.partZonotope V).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  have h : nominalSet (pZ.partZonotope V) = (nominal (pZ.partZonotope V)).construct := rfl
  refine ⟨y, ?_, e, he, rfl⟩
  rw [h, PolyZonotope.partZonotope_nominal]
  exact Real.PolyZonotope.partZonotope_outer (nominal pZ) V hy

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
