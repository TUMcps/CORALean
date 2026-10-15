module

public import CORALean.ContSet.Zonotope.Real.Operations.Rotate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost

@[expose] public section

/-!
# `Zonotope.rotateCost`

Asserted, not proved: `Operations/Rotate.lean` is `Zonotope.mtimes` at the plane
rotation `rotMat`, whose two nonzero entries cost a `cos` and a `sin`, priced
at one operation each, on top of `Zonotope.mtimesCost n n h`: the matrix is
applied dense, the zeros of the rotation not being exploited.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.rotate` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.rotateCost (n h : ℕ) : Cost := ⟨2⟩ + Zonotope.mtimesCost n n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
