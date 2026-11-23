module

public import CORALean.NN.Definitions.GraphNetFloat
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope

@[expose] public section

/-!
# `GraphNet.maxPool`

MaxPool as CORA.cpp builds it, in floats: the layer `relu(D x)` (CORALean's ReLU line at
`reluSlope`), then that output through the identity plus `B x` as a residual of the input. Its
outputs are `max((D + B) x, B x)` (`Real.GraphNet.maxPool_eval`), enclosed by
`GraphNet.maxPool_encloses`.

## Inputs
* `D` – the difference `A - B` of the operands' maps
* `B` – the second operand's map
* `slots` – whether the ReLU's errors become generators

## Output
* the network of the two layers
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GraphNet.maxPool (D B : Mat 𝕋 m n) (slots : Bool) : GraphNet 𝕋 [n] m :=
  -- 1. relu(D x), from the input
  .layer ⟨⟨0, Nat.succ_pos _⟩, D, fun _ => zero, [], .elementwise (reluRelaxation reluSlope) slots⟩
    -- 2. that output, plus B x from the input
    (.layer ⟨⟨0, Nat.succ_pos _⟩, (diagonalBlock fun _ => one : Mat 𝕋 m m), fun _ => zero,
      [⟨⟨1, Nat.lt_succ_self _⟩, B⟩], .identity⟩ .done)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
