import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.interval`

CORA's `@zonotope/interval`: the interval hull, `c ± ∑ⱼ |gⱼ|` per coordinate.

At `Vec ℝ n` only: a hull is read coordinatewise, so it needs an ambient type
that has coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Zonotope.interval (Z : Zonotope (Vec ℝ n)) : Interval n where
  inf := fun i => Z.c i - ∑ j, |Z.G j i|
  sup := fun i => Z.c i + ∑ j, |Z.G j i|

end CORALean.Real
