import CORALean.Real.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.interval`

CORA's `@zonotope/interval`: the interval hull, `c ± ∑ⱼ |gⱼ|` per coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Zonotope.interval (Z : Zonotope n) : Interval n where
  inf := fun i => Z.c i - ∑ j, |Z.G i j|
  sup := fun i => Z.c i + ∑ j, |Z.G i j|

end CORALean.Real
