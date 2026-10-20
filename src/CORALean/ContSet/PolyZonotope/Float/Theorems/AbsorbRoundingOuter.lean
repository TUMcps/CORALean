module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ZeroMemAbsorbRoundingErr

@[expose] public section

/-!
# `absorbRounding` loses no point

Read back through `ContSet`, for a caller that only wants the inclusion:
`absorbRounding_nominal` places every point in the nominal set, and the box denotes
the origin alone.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set lies in the absorbed one
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.absorbRounding_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.absorbRounding.construct := fun x hx =>
  ⟨x, PolyZonotope.absorbRounding_nominal pZ hx, 0,
    PolyZonotope.zero_mem_absorbRounding_err pZ, add_zero x⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
