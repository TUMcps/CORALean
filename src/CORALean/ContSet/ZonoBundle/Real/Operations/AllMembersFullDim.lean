import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import Mathlib.LinearAlgebra.Span.Defs

/-!
# `ZonoBundle.allMembersFullDim`

The first two tests of CORA's `@zonoBundle/isFullDim`: it answers `false` if a member
zonotope is not full-dimensional (its generators do not span the ambient space), the rank test of
`Zonotope.isFullDim`. Its last step, `isFullDim(polytope(zB))`, tests the intersection itself
and is not formalized. CORA also answers `false` for a bundle without members, whose `construct`
here is the whole space.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.allMembersFullDim (zB : ZonoBundle α) : Prop :=
  ∀ i, Submodule.span ℝ (Set.range (zB.Z i).G) = ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
