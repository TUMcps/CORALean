module

public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `interval(lb,ub)`

The one-dimensional `interval` with the bounds `lb` and `ub`, as the nodes store it.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (interval
arithmetic over `𝕋` with outward rounding) is not yet written.

## Inputs
* `lb` – lower bound
* `ub` – upper bound

## Output
* the one-dimensional interval with those bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval(lb,ub)`: the one-dimensional interval with the bounds `lb` and `ub`. -/
def SyntaxTree.interval (lb ub : ℝ) : Dom := ⟨fun _ => lb, fun _ => ub⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
