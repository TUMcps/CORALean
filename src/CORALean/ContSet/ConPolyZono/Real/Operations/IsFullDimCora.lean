import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `ConPolyZono.isFullDimCora`: CORA's test for full dimension

`@conPolyZono/isFullDim` answers `false` for the empty set and otherwise `rank([G GI]) == n`,
the same test as for a polynomial zonotope, and with the same flaw: the rank of the generators
says nothing about the constraints or the exponents (`isFullDim_cora_counterexample`). The rank
of a matrix is the dimension of the span of its columns. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Nonempty, and the generators of both blocks span a space of the ambient dimension. -/
def ConPolyZono.isFullDimCora (cPZ : ConPolyZono α) : Prop :=
  cPZ.construct.Nonempty
    ∧ Module.finrank ℝ (Submodule.span ℝ (Set.range cPZ.G ∪ Set.range cPZ.GI))
      = Module.finrank ℝ α

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
