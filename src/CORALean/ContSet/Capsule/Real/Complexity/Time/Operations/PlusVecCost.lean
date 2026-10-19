module

public import CORALean.ContSet.Capsule.Real.Operations.PlusVec
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.plusVecCost`

Asserted, not proved: `Operations/PlusVec.lean` shifts the center, `n` additions;
the generator and radius are copied into the result. The result's `2 * n + 1` scalars are all
written.

## Inputs
* `n` – dimension

## Output
* the cost of adding a vector to a capsule
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.plusVec` costs at `Vec ℝ n`: `n` additions for the center, and `2 * n + 1`
writes, the carried generator and radius included. -/
def Capsule.plusVecCost (n : ℕ) : Cost := ⟨n + (2 * n + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
