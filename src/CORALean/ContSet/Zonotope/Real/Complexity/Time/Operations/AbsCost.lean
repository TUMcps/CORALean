module

public import CORALean.ContSet.Zonotope.Real.Operations.Abs
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.absCost`

Asserted, not proved: `Operations/Abs.lean` takes the absolute value of every entry of the
center and of the generator matrix, `n * (h + 1)` of them, and writes each, `n * (h + 1)` more.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.abs` costs at `Vec ℝ n` and `h` generators: `n * (h + 1)` absolute values and
as many writes. -/
def Zonotope.absCost (n h : ℕ) : Cost := ⟨2 * (n * (h + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
