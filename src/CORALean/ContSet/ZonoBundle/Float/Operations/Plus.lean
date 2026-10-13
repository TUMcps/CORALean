import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `ZonoBundle.plus`

CORA's `zonoBundle`/`plus` at float zonotopes: every pair of members, one from
each bundle, summed by `Zonotope.plus` and indexed through `finProdFinEquiv`.

Two losses, and only the first is the float layer's: each pairwise sum rounds
its centre into the member's own error box, and — already over ℝ — a sum of
intersections is not an intersection of sums.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.plus (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    Zonotope.plus (zB₁.Z (finProdFinEquiv.symm p).1) (zB₂.Z (finProdFinEquiv.symm p).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
