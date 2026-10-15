module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffAlignedCost`

Asserted, not proved: `Operations/MinkDiffAligned.lean` subtracts the centres
and the `h` generators pairwise, `n * (h + 1)` subtractions at `Vec ℝ n`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffAligned` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.minkDiffAlignedCost (n h : ℕ) : Cost := ⟨n * (h + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
