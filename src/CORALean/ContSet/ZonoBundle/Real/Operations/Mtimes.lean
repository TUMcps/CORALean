module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ZonoBundle.mtimes`

CORA's `zonoBundle`/`mtimes`: the same `k`, each component multiplied on its
own [1, Prop. 1]. An enclosure, and a cheap one — exact when `M` is injective, though that
is not proved here.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
