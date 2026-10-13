module

public import CORALean.NN.Operations.IntervalChainFwd

@[expose] public section

/-!
# The interval batch backpropagation of an interval chain

CORA's `neuralNetwork/backpropIntervalBatch`, for one interval and with no weight update: from
the last layer to the first, each layer maps the gradients `(gl, gu)` at its output to ones at
its input, at the interval `[l, u]` it received. The linear layer's rule is `dmu = Wᵀ (gu + gl)/2`,
`dr = |W|ᵀ (gu - gl)/2`, `gl ← dmu - dr`, `gu ← dmu + dr`; the activation's, `gl ← σ'(l) ⊙ gl`,
`gu ← σ'(u) ⊙ gu`. The `updateWeights` branch stores the gradient of `W` and `b` in the layer
and returns nothing, so it is not here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def IntervalChain.backprop : ∀ {n k : ℕ}, IntervalChain n k →
    Vec ℝ n × Vec ℝ n → Vec ℝ k × Vec ℝ k → Vec ℝ n × Vec ℝ n
  | _, _, .nil, _, g => g
  | _, _, .linear W b rest, p, g =>
    let mu := W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + b
    let r := W.map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))
    let g' := rest.backprop (mu - r, mu + r) g
    let dmu := Wᵀ *ᵥ ((1 / 2 : ℝ) • (g'.2 + g'.1))
    let dr := (W.map abs)ᵀ *ᵥ ((1 / 2 : ℝ) • (g'.2 - g'.1))
    (dmu - dr, dmu + dr)
  | _, _, .act σ σ' rest, p, g =>
    let g' := rest.backprop (fun i => σ (p.1 i), fun i => σ (p.2 i)) g
    (fun i => σ' (p.1 i) * g'.1 i, fun i => σ' (p.2 i) * g'.2 i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
