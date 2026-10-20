module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.agreeRow`

The row pinning the two points together in one coordinate. Entries are
copied and `neg` is exact, so nothing here rounds.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand
* `i` – coordinate

## Output
* constraint row for that coordinate
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The row pinning the two points together in coordinate `i`. Entries are
copied and `neg` is exact, so nothing here rounds. -/
def ConPolyZono.agreeRow (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin n) :
    Fin (cPZ₁.h + cPZ₂.h) → 𝕋 :=
  Fin.append (fun l => cPZ₁.G l i) fun l => neg (cPZ₂.G l i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
