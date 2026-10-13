module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `rotMat`

The matrix of CORA's `@zonotope/rotate(Z, dims, angle)`: the 2x2 rotation `R = [cos -sin; sin cos]`
on the two coordinates `dims = (i, j)`, as an `n x n` matrix that is the identity elsewhere.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rotation by `angle` in the plane of coordinates `i` and `j` (CORA's `dims`), as an
`n x n` matrix: `[cos -sin; sin cos]` on those two, the identity elsewhere. -/
noncomputable def rotMat (n : ℕ) (i j : Fin n) (angle : ℝ) : Mat ℝ n n := fun a b =>
  if a = i then (if b = i then Real.cos angle else if b = j then -Real.sin angle else 0)
  else if a = j then (if b = i then Real.sin angle else if b = j then Real.cos angle else 0)
  else if a = b then 1 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
