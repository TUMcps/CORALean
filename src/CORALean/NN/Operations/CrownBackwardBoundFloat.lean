module

public import CORALean.NN.Operations.CrownBackwardFloat

@[expose] public section

/-!
# `CrownNet.backwardBound` in floats

CROWN's lower bound of `Λ · N(x)` over the box `|x - x₀| ≤ r`, in CORA.cpp's order
(`priv_backward_lower`): the backward pass's row `μ` at the box, `μ · x₀ - |μ| · r`, plus the
constant; less the rounding's slack and the input's gap at `|x₀| + r`, both `+0` at nearest. Sound
at every `SoundFloatArithmetic` by `CrownNet.backwardBound_le`.

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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def CrownNet.backwardBound (net : CrownNet 𝕋 n k) (Λ : Vec 𝕋 k) (x₀ r : Vec 𝕋 n) : 𝕋 :=
  -- 1. the backward pass
  let ρ := net.backward Λ
  -- 2. CORA.cpp's bound, `μ · x₀ - |μ| · r + c`
  let v := addDown (subDown (dotDown ρ.row x₀) (dotUp (fun j => absolute (ρ.row j)) r)) ρ.const
  -- 3. less the slack and the input's gap at `|x₀| + r`
  subDown v (addUp ρ.slack (dotUp ρ.gap fun j => addUp (absolute (x₀ j)) (r j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
