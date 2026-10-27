module

public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet

@[expose] public section

/-!
# `SetBasedNet.maxWidth`

`max_{k ∈ {0, …, κ}} n_k`, the largest width of a `SetBasedNet`, the input's included.
[1, Prop. 16] takes `n_max` over `k ∈ [κ]` alone, but its proof bounds the first layer's
`n₀ n₁ q` by `n_max² q`, which needs `n₀ ≤ n_max`.

## Inputs
* none

## Output
* widest layer of the network

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def SetBasedNet.maxWidth : {n k : ℕ} → SetBasedNet n k → ℕ
  | n, _, .output => n
  | n, _, .linear _ _ tail => max n tail.maxWidth
  | n, _, .nonlinear _ _ _ tail => max n tail.maxWidth

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
