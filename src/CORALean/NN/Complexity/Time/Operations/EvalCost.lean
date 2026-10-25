module

public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet
public import CORALean.Global.Cost

@[expose] public section

/-!
# `SetBasedNet.evalCost`

Asserted, not proved: what evaluating the network of [1, Def. 1] at one point costs, the check
`Φ(x̃) ∈ U` of [1, Alg. 1, l. 11] that [1, Prop. 4]'s proof counts. A linear layer `W h + b` at
`W ∈ ℝ^{m×n}` is one matrix-vector product and `m` additions; an activation applies `ϕ` to each
of its `n` neurons at `cEval` each. `SetBasedNet` carries the layers' enclosures, not `ϕ`, so
the price of `ϕ` is a parameter, as `cNeuron` is for `SetBasedNet.forwardCost`.

## Inputs
* `cEval` – cost of one activation at one neuron

## Output
* cost of evaluating the network at a point

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What evaluating the network at one point costs: per layer `W h + b` or `ϕ` per neuron. -/
def SetBasedNet.evalCost (cEval : Cost) : {n k : ℕ} → SetBasedNet n k → Cost
  | _, _, .output => 0
  | n, _, @SetBasedNet.linear _ m _ _ _ tail => Cost.matVec m n + ⟨m⟩ + tail.evalCost cEval
  | n, _, .nonlinear _ _ _ tail => n • cEval + tail.evalCost cEval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
