import CORALean.NN.Definitions.IntervalChain

/-!
# The forward pass of an interval chain

CORA's `evaluateInterval`, layer by layer: the linear layer's `mu = W μ + b`, `r = |W| r` read
back as `[mu - r, mu + r]`, the activation's `[σ l, σ u]`. The empty-set approximation-error
interval `d` the linear layer may carry is not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def IntervalChain.fwd : ∀ {n k : ℕ}, IntervalChain n k →
    Vec ℝ n × Vec ℝ n → Vec ℝ k × Vec ℝ k
  | _, _, .nil, p => p
  | _, _, .linear W b rest, p =>
    let mu := W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + b
    let r := W.map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))
    rest.fwd (mu - r, mu + r)
  | _, _, .act σ _ rest, p => rest.fwd (fun i => σ (p.1 i), fun i => σ (p.2 i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
