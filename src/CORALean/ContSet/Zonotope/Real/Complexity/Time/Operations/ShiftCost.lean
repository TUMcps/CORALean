module

public import CORALean.ContSet.Zonotope.Real.Operations.Shift
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.shiftCost`

Asserted, not proved: `Operations/Shift.lean` subtracts `w` from the centre,
`n` subtractions at `Vec ℝ n`; the generators are untouched.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.shift` costs at `Vec ℝ n`. -/
def Zonotope.shiftCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
