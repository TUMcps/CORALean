import CORALean.ContSet.Zonotope.Real.Operations.Shift
import CORALean.Global.Cost

/-!
# `Zonotope.shiftCost`

Asserted, not proved: `Operations/Shift.lean` subtracts `w` from the centre,
`n` subtractions at `Vec ℝ n`; the generators are untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.shift` costs at `Vec ℝ n`. -/
def Zonotope.shiftCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
