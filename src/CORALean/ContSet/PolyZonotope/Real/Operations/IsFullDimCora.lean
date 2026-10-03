import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `PolyZonotope.isFullDimCora`: CORA's test for full dimension

`@polyZonotope/isFullDim` answers `rank([G GI]) == n`, after a check for the empty set that
never fires here, a polynomial zonotope containing the point `α = 0`. The rank of a matrix is
the dimension of the span of its columns, which is how it is written. The test is necessary
and not sufficient: `isFullDim_cora_counterexample`. Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The span of the generators of both blocks has the dimension of the whole space. -/
def PolyZonotope.isFullDimCora (pZ : PolyZonotope α) : Prop :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range pZ.G ∪ Set.range pZ.GI)) = Module.finrank ℝ α

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
