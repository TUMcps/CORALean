module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.agreeCons`

The rows of `intersectionDep` that pin the two points together, as a polynomial level set on both
sets' factors: in coordinate `i`, the first set's dependent part minus the second's equals
`c₂ᵢ - c₁ᵢ`, read against both generator exponent matrices side by side (`agreeRow`).

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* constraint pinning the two points together
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One equation per coordinate on the factors' unit box: the two points agree there. -/
def ConPolyZono.agreeCons (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) : PolyLevelSet (cPZ₁.p + cPZ₂.p) :=
  ⟨n, cPZ₁.h + cPZ₂.h, fun i => ConPolyZono.agreeRow cPZ₁ cPZ₂ i,
    PolyZonotope.plusE cPZ₁.E cPZ₂.E, fun i => cPZ₂.c i - cPZ₁.c i, fun _ => .eq, Interval.unit _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
