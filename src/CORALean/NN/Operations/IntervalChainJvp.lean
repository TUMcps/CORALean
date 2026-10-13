module

public import CORALean.NN.Operations.IntervalChainFwd

@[expose] public section

/-!
# The tangent propagation of an interval chain

How a small change `δ = (δl, δu)` of the interval moves the output, layer by layer: the linear
layer's map is linear in `(l, u)`, the bias dropping out, and the activation scales each end by
the derivative there. It is the specification `IntervalChain.backprop` is the adjoint of.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def IntervalChain.jvp : ∀ {n k : ℕ}, IntervalChain n k →
    Vec ℝ n × Vec ℝ n → Vec ℝ n × Vec ℝ n → Vec ℝ k × Vec ℝ k
  | _, _, .nil, _, δ => δ
  | _, _, .linear W b rest, p, δ =>
    let mu := W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + b
    let r := W.map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))
    let dmu := W *ᵥ ((1 / 2 : ℝ) • (δ.1 + δ.2))
    let dr := W.map abs *ᵥ ((1 / 2 : ℝ) • (δ.2 - δ.1))
    rest.jvp (mu - r, mu + r) (dmu - dr, dmu + dr)
  | _, _, .act σ σ' rest, p, δ =>
    rest.jvp (fun i => σ (p.1 i), fun i => σ (p.2 i))
      (fun i => σ' (p.1 i) * δ.1 i, fun i => σ' (p.2 i) * δ.2 i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
