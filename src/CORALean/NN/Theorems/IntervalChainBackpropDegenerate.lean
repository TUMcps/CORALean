module

public import CORALean.NN.Operations.IntervalChainBackprop
public import CORALean.NN.Operations.IntervalChainToChain
public import CORALean.NN.Operations.Backprop
public import CORALean.NN.Theorems.SensitivityLinear
public import CORALean.NN.Theorems.SensitivityActivation

@[expose] public section

/-!
# The interval backpropagation at a point is the gradient

On the degenerate input pair `(x, x)` and output pair `(g, g)` the interval backpropagation of a
smooth chain returns `(Chain.backprop c x g, Chain.backprop c x g)` for the chain of its layers'
functions: the radius `|W| r` of every linear layer is zero, so `dr = 0` and the two bounds meet at
`Wᵀ g`, and an activation multiplies by `σ'(x)`, the entry of the layer's Jacobian.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* for a chain whose activations have the stored derivatives, both bounds are the point
  backpropagation of the chain of the layers' functions
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Real.IntervalChain.backprop_degenerate : -- --- CONCL ---
    ∀ {n k : ℕ} (c : Real.IntervalChain n k) (_hs : c.IsSmooth) (x : Vec ℝ n) (g : Vec ℝ k),
    c.backprop (x, x) (g, g) =
      (c.toChain.backprop x g, c.toChain.backprop x g) := by -- --- PROOF ---
  intro n k c
  induction c with
  | nil => intro _ x g; rfl
  | linear W b rest ih =>
    -- the radius of the layer is zero, both bounds being `W x + b`
    intro hs x g
    have h := ih hs (W *ᵥ x + b) g
    have hx : (1 / 2 : ℝ) • (x + x) = x := by
      rw [← two_smul ℝ x, smul_smul]; norm_num
    simp only [Real.IntervalChain.backprop, Real.IntervalChain.toChain, Chain.backprop,
      Layer.linear_sensitivity, hx, sub_self, smul_zero, Matrix.mulVec_zero, sub_zero,
      add_zero]
    rw [h]
    simp only [sub_self, smul_zero, Matrix.mulVec_zero, sub_zero, add_zero]
    congr 1 <;> (congr 1; rw [← two_smul ℝ, smul_smul]; norm_num)
  | act σ σ' rest ih =>
    -- the activation multiplies by the diagonal Jacobian `σ'(x)`
    intro hs x g
    have h := ih hs.2 (fun i => σ (x i)) g
    simp only [Real.IntervalChain.backprop, Real.IntervalChain.toChain, Chain.backprop,
      Layer.activation_sensitivity hs.1]
    rw [h]
    simp only [Matrix.diagonal_transpose]
    congr 1 <;> (ext i; rw [Matrix.mulVec_diagonal])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
