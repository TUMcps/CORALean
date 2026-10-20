module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffStretchCost`

Asserted, not proved: `Operations/MinkDiffStretch.lean` subtracts the centers
(`n`) and scales each of the `h` generators of the minuend by its `μ i`
(`n * h`).

Under `Global/Cost.lean`'s model every scalar of the result is also a write, one unit each, and the
result's `n * (h + 1)` entries are
written once each.

## Inputs
* `n` – dimension
* `h` – generator count

## Output
* cost of the operations and writes, `2n(h+1)`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffStretch` costs at `Vec ℝ n` and `h` generators: `n * (h + 1)`
arithmetic operations and as many writes. -/
def Zonotope.minkDiffStretchCost (n h : ℕ) : Cost := ⟨2 * (n * (h + 1))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
