module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.methCResidual`

What a candidate inverse `H` of a basis `P` is held to: an upper bound on `|1 - H P|`
entry by entry. The product's entries are dot products, each in both directions, so
`1 - (H P)ᵢⱼ` lies between the two differences, and the larger magnitude of those bounds the entry
whichever sign it has.

## Inputs
* `H` – candidate right inverse
* `P` – basis matrix

## Output
* entrywise upper bound on the residual
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound on `|1 - H P|`, entrywise. -/
def Zonotope.methCResidual (H P : Mat 𝕋 n n) : Fin n → Fin n → 𝕋 := fun i j =>
  maximum
    (absolute (subDown (if i = j then one else zero) (dotUp (H i) fun l => P l j)))
    (absolute (subUp (if i = j then one else zero) (dotDown (H i) fun l => P l j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
