import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `ConZonotope.isFullDimCora`

CORA's `@conZonotope/isFullDim` as the code computes it: without constraints the rank test of the
zonotope `(c, G)`; with them `T = null(A)`, `rank(G T) == n`. The null space `T` of the equality
rows is the set of coefficient vectors `ξ` with `Aₑ ξ = 0`, so the test asks that the generators
applied to it span all of `ℝⁿ`. Inequality rows (CORA has none) are not read, and `b` and the
unit box are not read either, which is why this is only a necessary condition for the set to have
an interior; see `isFullDim_cora_counterexample`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `rank(G T) = n` for `T` a basis of the null space of the equality rows. -/
def ConZonotope.isFullDimCora (cZ : ConZonotope (Vec ℝ n)) : Prop :=
  Module.finrank ℝ (Submodule.span ℝ
      {v : Vec ℝ n | ∃ ξ : Vec ℝ cZ.h, (∀ i, cZ.P.Ae i ξ = 0) ∧ v = ∑ j, ξ j • cZ.G j}) = n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
