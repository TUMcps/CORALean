module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost
public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetDepth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetMaxWidth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetNeurons
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `SetBasedNet.forwardCost`

Asserted, not proved, as [1, Prop. 16]'s proof counts `SetBasedNet.forward`: a linear layer
`W H + b` at `Zonotope.mtimesCost m n h` and `Zonotope.plusCost m h 0`, a nonlinear one at
`Zonotope.imageEnclosureCost`, whose `n` new generators the next layer carries. The proved part is
`O(n_max² q κ)`: at most `(cNeuron + 17) N² Q κ` for `N` at least every width and `Q` at least
`h + Σₖ nₖ`. `N` has to cover the input width `n₀` too: with `n_max` over `k ∈ [κ]` alone, as
printed, a wide input (`n₀ = N`, one linear layer to `n₁ = 1`, `q = N`) costs `2N(N + 1) + 1`
against `n_max² q κ = N`, so no constant independent of `n₀` bounds it.

## Inputs
* `cNeuron` – cost of one neuron

## Output
* cost of a forward pass from a given generator count

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `SetBasedNet.forward` costs from an input set with `h` generators. -/
def SetBasedNet.forwardCost (cNeuron : Cost) : {n k : ℕ} → SetBasedNet n k → ℕ → Cost
  | _, _, .output, _ => 0
  | n, _, @SetBasedNet.linear _ m _ _ _ tail, h =>
      Zonotope.mtimesCost m n h + Zonotope.plusCost m h 0 + tail.forwardCost cNeuron h
  | n, _, .nonlinear _ _ _ tail, h =>
      Zonotope.imageEnclosureCost n h cNeuron + tail.forwardCost cNeuron (h + n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
