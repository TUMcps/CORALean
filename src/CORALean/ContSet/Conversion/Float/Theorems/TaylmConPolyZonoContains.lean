module

public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeConPolyZonoContains
public import CORALean.ContSet.Conversion.Float.Theorems.TaylmPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# An array of Taylor models as a constrained polynomial zonotope, over a floating-point scalar

CORA's `conPolyZono(taylm)`: the polynomial zonotope of the models with no constraint. The
composition of the two float conversions, so the remainder box is the error box and nothing
rounds. The range set is contained.

## Inputs
* `T` – Taylor models, one per coordinate

## Hypotheses
* none

## Conclusion
* Taylor models are contained in their constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.conPolyZono_contains (T : Fin m → Taylm 𝕋 n) :
    Taylm.construct T ⊆ (Taylm.conPolyZono T).construct :=
  (Taylm.polyZonotope_contains T).trans (PolyZonotope.conPolyZono_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
