module

public import CORALean.ContSet.Capsule.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the centers (`n`), forms the
two squared lengths `∑ g i ^ 2` (`2 * n` each: `n` products and `n` additions),
compares them (`1`), and in the taken branch adds the radii and the root of the
shorter length (`2` additions and one `sqrt`). A `sqrt` is priced as one
operation, like a division. Bounded above by evaluating both lengths and the
root: `n + 4 * n + 1 + 3 = 5 * n + 4`.

The result is the center, the kept generator and the radius, `2 * n + 1` writes.

## Inputs
* `n` – dimension

## Output
* the cost of adding two capsules
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.plus` costs at `Vec ℝ n`, and `2 * n + 1` writes for the center, the kept
generator and the radius. -/
def Capsule.plusCost (n : ℕ) : Cost := ⟨5 * n + 4 + (2 * n + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
