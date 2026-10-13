import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Operations.CartProd
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `ZonoBundle.cartProd`

CORA's `@zonoBundle/cartProd_` for two bundles: the list of all pairs, `cartProd_(zB.Z{i},
S.Z{j},'exact')`, with `i` the outer and `j` the inner loop, which is the flattening
`finProdFinEquiv` of the index pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle/cartProd_` at a bundle. -/
def ZonoBundle.cartProd (zB₁ : ZonoBundle α) (zB₂ : ZonoBundle β) : ZonoBundle (α × β) where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    let ij := finProdFinEquiv.symm p
    (zB₁.Z ij.1).cartProd (zB₂.Z ij.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
