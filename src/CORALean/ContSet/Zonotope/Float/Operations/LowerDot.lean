import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.lowerDot`

A float that no point of the zonotope's support falls below: the *lower* counterpart of
`boundDot`'s upper bounds, for a number that is subtracted. The support of
`c ⊕ G[-1,1]ʰ ⊕ E` in direction `a` is `aᵀc + Σⱼ |aᵀGⱼ| + Σᵢ max(aᵢ E.infᵢ, aᵢ E.supᵢ)`; each
term is rounded down, a generator's `|aᵀGⱼ|` through the enclosure `[dotDown, dotUp]` of
`aᵀGⱼ`, as `max(0, lo, -hi)`, and the error box's term at its smaller end.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aᵀc + Σⱼ |aᵀGⱼ| + Σᵢ min(aᵢ E.infᵢ, aᵢ E.supᵢ)`, every rounding downward. -/
def Zonotope.lowerDot (Z : Zonotope 𝕋 n) (a : Vec 𝕋 n) : 𝕋 :=
  let centre := dotDown a Z.c                                       -- aᵀc
  let gens := sumDown fun j => maximum zero                         -- Σⱼ |aᵀGⱼ|, from below
    (maximum (dotDown a fun i => Z.G i j) (neg (dotUp a fun i => Z.G i j)))
  let box := sumDown fun i =>                                       -- Σᵢ aᵢ eᵢ, at the smaller end
    minimum (mulDown (a i) (Z.E.inf i)) (mulDown (a i) (Z.E.sup i))
  addDown (addDown centre gens) box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
