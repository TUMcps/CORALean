import CORALean.Float.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.interval`

CORA's `@zonotope/interval`: the hull `c ± radius G`, inflated by the box. An
`Interval` has no box, so the bounds themselves absorb every rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.interval (Z : Zonotope 𝕋 n) : Interval 𝕋 n where
  inf := fun i => addDown (subDown (Z.c i) (radius Z.G i)) (Z.E.inf i)
  sup := fun i => addUp (addUp (Z.c i) (radius Z.G i)) (Z.E.sup i)

end CORALean.Float
