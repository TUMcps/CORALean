module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffStretchCost`

Asserted, not proved: `Operations/MinkDiffStretch.lean` subtracts the centers
(`n`) and scales each of the `h` generators of the minuend by its `μ i`
(`n * h`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffStretch` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.minkDiffStretchCost (n h : ℕ) : Cost := ⟨n * (h + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
