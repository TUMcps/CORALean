module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffAlignedCost`

Asserted, not proved: `Operations/MinkDiffAligned.lean` subtracts the centers
and the `h` generators pairwise, `n * (h + 1)` subtractions at `Vec ℝ n`.

Under `Global/Cost.lean`'s model every scalar of the result is also a write, one unit each, and the
result's `n * (h + 1)` entries are
written once each.

## Inputs
* `n` – dimension
* `h` – generator count

## Output
* cost of the subtractions and writes, `2n(h+1)`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffAligned` costs at `Vec ℝ n` and `h` generators: `n * (h + 1)`
subtractions and as many writes. -/
def Zonotope.minkDiffAlignedCost (n h : ℕ) : Cost := ⟨2 * (n * (h + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
