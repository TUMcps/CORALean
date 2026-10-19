module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.agreeCons`

The rows of `intersectionDep` that pin the two points together, as a polynomial level set on both
sets' factors: in coordinate `i`, the first set's dependent part minus the second's equals
`c₂ᵢ - c₁ᵢ`, read against both generator exponent matrices side by side (`agreeRow`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One equation per coordinate: the two points agree there. -/
def ConPolyZono.agreeCons (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) : PolyLevelSet (cPZ₁.p + cPZ₂.p) :=
  ⟨n, cPZ₁.h + cPZ₂.h, fun i => ConPolyZono.agreeRow cPZ₁ cPZ₂ i,
    PolyZonotope.plusE cPZ₁.E cPZ₂.E, fun i => cPZ₂.c i - cPZ₁.c i, fun _ => .eq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
