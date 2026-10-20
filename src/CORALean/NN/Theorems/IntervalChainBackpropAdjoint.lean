module

public import CORALean.NN.Operations.IntervalChainBackprop
public import CORALean.NN.Operations.IntervalChainJvp

@[expose] public section

/-!
# The interval backpropagation is the adjoint of the tangent propagation

For every gradient `g` at the output and every change `δ` of the input interval, the gradient
`backprop` returns, paired with `δ`, is `g` paired with where `jvp` sends `δ`. That is what
"the transposed Jacobian" says without a Jacobian: each layer's rule is the transpose of its
tangent rule, and the chain composes them in opposite orders. The linear layer's `dmu - dr`,
`dmu + dr` is the transpose of `(dmu - dr, dmu + dr)` in `δ`, with `|W|` held fixed; the
activation's is a diagonal map, its own transpose.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* interval backpropagation is the adjoint of the tangent propagation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.backprop_adjoint : ∀ {n k : ℕ} (c : IntervalChain n k)
    (p δ : Vec ℝ n × Vec ℝ n) (g : Vec ℝ k × Vec ℝ k),
    (c.backprop p g).1 ⬝ᵥ δ.1 + (c.backprop p g).2 ⬝ᵥ δ.2
      = g.1 ⬝ᵥ (c.jvp p δ).1 + g.2 ⬝ᵥ (c.jvp p δ).2 := by -- --- PROOF ---
  intro n k c
  induction c with
  | nil => intro p δ g; rfl
  | linear W b rest ih =>
    -- the transpose moves across a product, so each layer's rule is its tangent rule's adjoint
    intro p δ g
    have key : ∀ {a b : ℕ} (M : Mat ℝ a b) (x : Vec ℝ a) (y : Vec ℝ b),
        (Mᵀ *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (M *ᵥ y) := fun M x y => by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    have h := ih (W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + b - W.map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1)),
      W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + b + W.map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1)))
      (W *ᵥ ((1 / 2 : ℝ) • (δ.1 + δ.2)) - W.map abs *ᵥ ((1 / 2 : ℝ) • (δ.2 - δ.1)),
       W *ᵥ ((1 / 2 : ℝ) • (δ.1 + δ.2)) + W.map abs *ᵥ ((1 / 2 : ℝ) • (δ.2 - δ.1))) g
    -- the rest of the chain by induction, then the layer's own pairing
    simp only [IntervalChain.backprop, IntervalChain.jvp]
    rw [← h]
    simp only [sub_dotProduct, add_dotProduct, key, dotProduct_sub, dotProduct_add,
      dotProduct_smul, smul_dotProduct, Matrix.mulVec_add, Matrix.mulVec_sub,
      Matrix.mulVec_smul, smul_eq_mul]
    ring
  | act σ σ' rest ih =>
    intro p δ g
    have h := ih (fun i => σ (p.1 i), fun i => σ (p.2 i))
      (fun i => σ' (p.1 i) * δ.1 i, fun i => σ' (p.2 i) * δ.2 i) g
    simp only [IntervalChain.backprop, IntervalChain.jvp]
    rw [← h]
    simp only [dotProduct]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
