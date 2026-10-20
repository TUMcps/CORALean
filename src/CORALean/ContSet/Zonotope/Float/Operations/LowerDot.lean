module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.lowerDot`

A float that no point of the zonotope's support falls below: the *lower* counterpart of
`boundDot`'s upper bounds, for a number that is subtracted. The support of
`c ⊕ G[-1,1]ʰ ⊕ E` in direction `a` is `aᵀc + Σⱼ |aᵀGⱼ| + Σᵢ max(aᵢ E.infᵢ, aᵢ E.supᵢ)`; each
term is rounded down, a generator's `|aᵀGⱼ|` through the enclosure `[dotDown, dotUp]` of
`aᵀGⱼ`, as `max(0, lo, -hi)`, and the error box's term at its smaller end.

## Inputs
* `Z` – zonotope
* `a` – direction

## Output
* lower bound of the direction's dot product over the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aᵀc + Σⱼ |aᵀGⱼ| + Σᵢ min(aᵢ E.infᵢ, aᵢ E.supᵢ)`, every rounding downward. -/
def Zonotope.lowerDot (Z : Zonotope (Vec 𝕋 n)) (a : Vec 𝕋 n) : 𝕋 :=
  let center := dotDown a Z.c                                       -- aᵀc
  let gens := sumDown fun j => maximum zero                         -- Σⱼ |aᵀGⱼ|, from below
    (maximum (dotDown a (Z.G j)) (neg (dotUp a (Z.G j))))
  let box := sumDown fun i =>                                       -- Σᵢ aᵢ eᵢ, at the smaller end
    minimum (mulDown (a i) (Z.I_error.inf i)) (mulDown (a i) (Z.I_error.sup i))
  addDown (addDown center gens) box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
