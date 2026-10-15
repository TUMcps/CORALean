module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.BilinCost

@[expose] public section

/-!
# `Zonotope.mtimesMatZonotopeCost`

Asserted, not proved: `Operations/MtimesMatZonotope.lean` is `Zonotope.bilin` at
matrix-vector application, one `Cost.matVec m n` per application.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimesMatZonotope` costs at `M : Zonotope (Mat ℝ m n)` of `hM`
generators and `Z` of `h`. -/
def Zonotope.mtimesMatZonotopeCost (m n hM h : ℕ) : Cost :=
  Zonotope.bilinCost (Cost.matVec m n) hM h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
