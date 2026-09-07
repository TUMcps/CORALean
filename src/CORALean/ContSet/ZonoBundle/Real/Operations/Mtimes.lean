import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `ZonoBundle.mtimes`

CORA's `zonoBundle`/`mtimes`: the same `k`, each component multiplied on its
own. An enclosure, and a cheap one — exact when `M` is injective, though that
is not proved here.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.mtimes (M : Mat ℝ m n) (zB : ZonoBundle (Vec ℝ n)) : ZonoBundle (Vec ℝ m) where
  k := zB.k
  Z := fun i => Zonotope.mtimes M (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
