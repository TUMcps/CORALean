module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# `Zonotope.vertices`

CORA's `@matZonotope/vertices`: the vertices of `zonotope(matZ)` as matrices, without repetition
(`unique`). CORA lists the extreme points; the Lean list is the corners one sign per generator picks
out (`Zonotope.corner`), a superset of them with the same convex hull, as for the vector class.
Generic over the ambient type, so at `Mat ℝ m n` it is the matrix zonotope's.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The corners of the zonotope, without repetition. -/
noncomputable def Zonotope.vertices (Z : Zonotope α) : Finset α :=
  Finset.univ.image Z.corner

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
