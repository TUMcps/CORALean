module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `ZonoBundle.linComb`

Every pair of zonotopes, one from each bundle, combined by `Zonotope.linComb`
and indexed through `finProdFinEquiv`, exactly as `plus` sums pairs. Also an
enclosure, but for a different reason: `plus`'s loss is that a sum of
intersections is not an intersection of sums, while here the interpolation
weight `lam` is genuinely shared across every pair — only the endpoints vary.
Whether that makes this tighter than `plus` in practice is not claimed here.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Output
* enclosure of the convex hull
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ZonoBundle.linComb (zB₁ zB₂ : ZonoBundle α) : ZonoBundle α where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    Zonotope.linComb (zB₁.Z (finProdFinEquiv.symm p).1) (zB₂.Z (finProdFinEquiv.symm p).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
