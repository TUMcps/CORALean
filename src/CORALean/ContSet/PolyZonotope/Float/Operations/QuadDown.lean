module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `g ⬝ᵥ w` rounded down, `w` known only to lie in an interval

Split out of `QuadMap.lean` (issue #62): read again by
`Theorems/QuadDownLe.lean`, outside this file.

## Inputs
* `g` – vector
* `wlo` – lower bound of the second vector
* `whi` – upper bound of the second vector

## Output
* lower bound of the dot product, rounded down
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g ⬝ᵥ w` rounded down, where `w` is known only to lie in `[wlo, whi]`. -/
def PolyZonotope.quadDown (g wlo whi : Vec 𝕋 n) : 𝕋 :=
  sumDown fun r => minimum (mulDown (g r) (wlo r)) (mulDown (g r) (whi r))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
