module

public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent

@[expose] public section

/-!
# `ConPolyZono.intersection`

Here a set is a nominal one plus an error box, so the points that have to agree are `y₁ + e₁` and
`y₂ + e₂`, and the rows can only speak about the nominal points. These differ by `e₂ - e₁`, so the
rows say they agree to within `c₂ − c₁ + [err₂.inf − err₁.sup, err₂.sup − err₁.inf]`, each end
rounded outward, recorded as a right-hand side `b` with slack `b_error`.

The result keeps `cPZ₁`'s error box and generator block; `cPZ₂` enters through the constraints
alone.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* enclosure of the intersection
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.intersection (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  ConPolyZono.intersectionDep cPZ₁.dependent cPZ₂.dependent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
