import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `ZonoBundle.plus`

CORA's `zonoBundle`/`plus`: every pair of zonotopes, one from each bundle,
summed and indexed through `finProdFinEquiv`. An *enclosure*, never exact — a
sum of intersections is not an intersection of sums, and nothing here records
that the same point of each intersection was the one summed in every pair.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.plus (B₁ B₂ : ZonoBundle α) : ZonoBundle α where
  k := B₁.k * B₂.k
  Z := fun p =>
    Zonotope.plus (B₁.Z (finProdFinEquiv.symm p).1) (B₂.Z (finProdFinEquiv.symm p).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
