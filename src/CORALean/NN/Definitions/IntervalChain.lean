module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# A network of interval layers, for the interval batch backpropagation

CORA's `neuralNetwork/backpropIntervalBatch` runs `layer.backpropIntervalBatch` from the last
layer to the first, each on the interval `[l, u]` the layer received in the forward pass. Two
layer kinds have the rule written out in the sources read for this row: the linear layer
(interval bound propagation: center `W μ + b`, radius `|W| r`) and the activation layer (`gl ←
f'(l) ⊙ gl`, `gu ← f'(u) ⊙ gu`, which is the rule of a monotonically increasing activation, the
images of `l` and `u` being its bounds). A chain of those two is `IntervalChain`. The activation
carries its function and its derivative as data, `σ'` being what CORA's `df` is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- A network of interval layers for backpropagation: the identity, a linear layer, or an
elementwise activation given with its derivative. -/
inductive IntervalChain : ℕ → ℕ → Type where
  | nil {n : ℕ} : IntervalChain n n
  | linear {n m k : ℕ} (W : Mat ℝ m n) (b : Vec ℝ m) (rest : IntervalChain m k) :
      IntervalChain n k
  | act {n k : ℕ} (σ σ' : ℝ → ℝ) (rest : IntervalChain n k) : IntervalChain n k

/-- That the activations' stored derivatives are derivatives, which is what the tangent
propagation being the derivative needs. -/
def IntervalChain.IsSmooth : ∀ {n k : ℕ}, IntervalChain n k → Prop
  | _, _, .nil => True
  | _, _, .linear _ _ rest => rest.IsSmooth
  | _, _, .act σ σ' rest => (∀ x, HasDerivAt σ (σ' x) x) ∧ rest.IsSmooth

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
