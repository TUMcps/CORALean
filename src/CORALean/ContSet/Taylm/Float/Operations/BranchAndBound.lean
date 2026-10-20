module

public import CORALean.ContSet.Taylm.Float.Operations.BnbLoop
public import CORALean.ContSet.Taylm.Float.Operations.ReexpBoxBounds

@[expose] public section

/-!
# `Taylm.branchAndBound`, over a floating-point scalar

The branch and bound of the ARCH 2018 listing over a box `X`: one box `[x]`, bounded on each
sub-box by interval evaluation of the term list (`polyBoxBounds`).

## Inputs
* `P` – terms of the polynomial
* `X` – domain box
* `ε` – tolerance
* `adv` – advanced bounding flag
* `fuel` – step budget

## Output
* enclosure of the polynomial's range
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.branchAndBound (P : List (𝕋 × (Fin n → ℕ))) (X : Fin n → Interval 𝕋) (ε : 𝕋) (adv : Bool)
    (fuel : ℕ) : Interval 𝕋 :=
  -- 15-16, 22-23, 28-29: a sub-box's bound, re-expanded first in the advanced setting
  let bnd := fun B => if adv then Taylm.reexpBoxBounds P B else Taylm.polyBoxBounds P B
  -- 2-5: one box, `[x]` itself
  Taylm.bnbLoop bnd ε fuel [X]
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
