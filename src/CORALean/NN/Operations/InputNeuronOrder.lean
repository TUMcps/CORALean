import CORALean.NN.Definitions.InputOrderMethod
import CORALean.NN.Operations.SnakeOrder
import CORALean.NN.Operations.Sensitivity

/-!
# `getInputNeuronOrder`

CORA's ranking of the input neurons, as a list of 0-based neuron indices (CORA's are 1-based):

* `inOrder`: the neurons in their own order;
* `snake`: the inward spiral over the `h × w` image, laid out column by column as MATLAB's
  `reshape` does (`snakeOrder`); CORA requires `inputSize` here, and without it the order is empty;
* `sensitivity`: the least sensitive neuron first, the sensitivity being the mean over the outputs
  of the absolute entries of `calcSensitivity` (`Chain.sensitivity`) and, given an
  `inputSize = (h, w, c)`, further the mean over the `c` channels, so only `h * w` neurons are
  ranked. The sort is stable, as MATLAB's.

Without `inputSize` the neurons are the `n` entries of the point `x`; with it, the first `h * w`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Classical


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def getInputNeuronOrder {n m : ℕ} (c : Chain n m) (method : InputOrderMethod)
    (x : Vec ℝ n) (inputSize : Option (ℕ × ℕ × ℕ)) : List ℕ :=
  match method with
  | .inOrder => List.range (match inputSize with | none => n | some (h, w, _) => h * w)
  | .snake =>
    match inputSize with
    | none => []
    | some (h, w, _) => snakeOrder h w fun i j => (i : ℕ) + h * j
  | .sensitivity =>
    -- the sensitivity, and its mean over the output neurons of the absolute entries
    let S := c.sensitivity x
    let S₁ : ℕ → ℝ := fun j => if hj : j < n then (∑ i, |S i ⟨j, hj⟩|) / m else 0
    match inputSize with
    | none => (List.range n).mergeSort fun a b => decide (S₁ a ≤ S₁ b)
    | some (h, w, ch) =>
      -- the mean across channels
      let S₂ : ℕ → ℝ := fun p => (∑ k ∈ Finset.range ch, S₁ (p + h * w * k)) / ch
      (List.range (h * w)).mergeSort fun a b => decide (S₂ a ≤ S₂ b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
