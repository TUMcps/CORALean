module

public import CORALean.NN.Definitions.CrownNet

@[expose] public section

/-!
# `CrownNet.backward`

CROWN's backward pass, in CORA.cpp's order (`priv_backward_lower`): a row `Λ` on the outputs
travels to the inputs, through an affine map as `Wᵀ Λ` with `Λ · b` into the constant, through an
activation as `Λ⁺ s_l + Λ⁻ s_u` with `Λ⁺ · b_l + Λ⁻ · b_u` into the constant (a positive weight
takes the lower line, a negative one the upper). The last layer is passed first, so each layer's
share is added to the constant of the layers after it.

## Inputs
* none

## Output
* the row on the inputs and the constant
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def CrownNet.backward : {n k : ℕ} → CrownNet n k → Vec ℝ k → Vec ℝ n × ℝ
  | _, _, .nil, Λ => (Λ, 0)
  | _, _, .linear W b rest, Λ =>
    -- 1. the row on the map's outputs, from the layers after it
    let ν := (rest.backward Λ).1
    -- 2. the constant gains `ν · b`, the row becomes `Wᵀ ν`
    ((fun j => ∑ i, ν i * W i j), (rest.backward Λ).2 + ∑ i, ν i * b i)
  | _, _, .act _ _ _ sl bl su bu rest, Λ =>
    -- 1. the row on the activation's outputs, from the layers after it
    let ν := (rest.backward Λ).1
    -- 2. the constant gains `ν⁺ · b_l + ν⁻ · b_u`, the row becomes `ν⁺ s_l + ν⁻ s_u`
    ((fun i => max (ν i) 0 * sl i + min (ν i) 0 * su i),
      (rest.backward Λ).2 + ∑ i, (max (ν i) 0 * bl i + min (ν i) 0 * bu i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
