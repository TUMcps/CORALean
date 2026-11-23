module

public import CORALean.NN.Operations.CrownBackward

@[expose] public section

/-!
# `CrownNet.backwardBound`

CROWN's lower bound of `Λ · N(x)` over the box `|x - x₀| ≤ r`: the backward pass's row `μ` on the
inputs at the box, `μ · x₀ - |μ| · r`, plus its constant. CORA.cpp's `priv_backward_lower`; sound
by `CrownNet.backwardBound_le`.

## Inputs
* `net` – the network
* `Λ` – the row on the outputs
* `x₀` – the box's center
* `r` – the box's radius

## Output
* the lower bound of the row on the network's outputs
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def CrownNet.backwardBound (net : CrownNet n k) (Λ : Vec ℝ k) (x₀ r : Vec ℝ n) :
    ℝ :=
  -- 1. the backward pass
  let μ := (net.backward Λ).1
  -- 2. the row at the box, plus the constant
  ∑ j, μ j * x₀ j - ∑ j, |μ j| * r j + (net.backward Λ).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
