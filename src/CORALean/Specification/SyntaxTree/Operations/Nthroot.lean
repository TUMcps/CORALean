module

public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `aux_nthroot_`

MATLAB's `nthroot(x,k)`: the real `k`-th root, negative arguments allowed for odd `k`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (interval
arithmetic over `𝕋` with outward rounding) is not yet written.

## Inputs
* `x` – real number
* `k` – degree

## Output
* the real root of that degree
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nthroot(x,k)`: the real `k`-th root of `x`. -/
noncomputable def SyntaxTree.nthroot (x : ℝ) (k : ℕ) : ℝ :=
  if 0 ≤ x then x ^ ((1 : ℝ) / k) else -((-x) ^ ((1 : ℝ) / k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
