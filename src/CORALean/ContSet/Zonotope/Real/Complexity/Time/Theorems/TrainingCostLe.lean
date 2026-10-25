module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ForwardCost
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.TrainingCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.TrainingCostLeSucc

@[expose] public section

/-!
# `SetBasedNet.trainingCost_le`

[1, Prop. 17]: `O(n_max² q κ)`, at most `2 C N² Q κ` for `κ ≥ 1`,
`C = cNeuron + 2 cBack + 2 cGrad + 50`.

## Inputs
* `cNeuron` – cost of one neuron
* `cGrad` – cost of one gradient step
* `cBack` – cost of one backpropagation step
* `N` – width bound
* `Q` – generator bound
* `n` – input dimension
* `k` – output dimension
* `net` – set-based network
* `h` – input generator count

## Hypotheses
* `hN` – width bound positive
* `hh` – input generators present
* `hw` – network width within the bound
* `hq` – generator total within the bound
* `hκ` – depth positive

## Conclusion
* training cost is at most `2C N² Q` times the depth

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 17]: `O(n_max² q κ)`, at most `2 C N² Q κ` for `κ ≥ 1`,
`C = cNeuron + 2 cBack + 2 cGrad + 50`. -/
theorem SetBasedNet.trainingCost_le (cNeuron cGrad cBack : Cost) {N Q : ℕ} (hN : 1 ≤ N)
    {n k : ℕ} (net : SetBasedNet n k) (h : ℕ) (hh : 1 ≤ h) (hw : net.maxWidth ≤ N)
    (hq : h + net.neurons ≤ Q) (hκ : 1 ≤ net.depth) : -- --- CONCL ---
    (net.trainingCost cNeuron cGrad cBack h).ops ≤
      2 * (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 50) * (N * N * Q) *
        net.depth := by -- --- PROOF ---
  have h1 := SetBasedNet.trainingCost_le_succ cNeuron cGrad cBack hN net h hh hw hq
  have h2 : net.depth + 1 ≤ 2 * net.depth := by omega
  calc (net.trainingCost cNeuron cGrad cBack h).ops
      ≤ (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 50) * (N * N * Q) * (net.depth + 1) := h1
    _ ≤ (cNeuron.ops + 2 * cBack.ops + 2 * cGrad.ops + 50) * (N * N * Q) * (2 * net.depth) :=
        Nat.mul_le_mul_left _ h2
    _ = _ := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
