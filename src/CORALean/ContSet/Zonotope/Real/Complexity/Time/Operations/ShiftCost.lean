module

public import CORALean.ContSet.Zonotope.Real.Operations.Shift
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.shiftCost`

Asserted, not proved: `Operations/Shift.lean` subtracts `w` from the center,
`n` subtractions at `Vec ℝ n`; the generators are untouched.

## Inputs
* `n` – dimension
* `h` – generator count

## Output
* `n` subtractions plus `n(h+1)` writes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.shift` costs at `Vec ℝ n` on `h` generators: `n` subtractions for the center
and `n * (h + 1)` writes for the result. -/
def Zonotope.shiftCost (n h : ℕ) : Cost := ⟨n + n * (h + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
