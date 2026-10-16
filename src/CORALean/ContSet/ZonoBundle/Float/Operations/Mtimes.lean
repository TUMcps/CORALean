module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# `ZonoBundle.mtimes`

CORA's `zonoBundle`/`mtimes` at float zonotopes: the same `k`, each member
multiplied on its own, so the rounding of the product lands in that member's
error box and never in a bundle-wide one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.mtimes (M : Mat 𝕋 m n) (zB : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 m) where
  k := zB.k
  Z := fun i => Zonotope.mtimes M (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
