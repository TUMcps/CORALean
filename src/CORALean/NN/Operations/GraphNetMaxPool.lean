module

public import CORALean.NN.Definitions.GraphNet
public import Mathlib.Data.Matrix.Diagonal
public import CORALean.NN.Layers.Definitions.Relu

@[expose] public section

/-!
# `GraphNet.maxPool`

MaxPool as CORA.cpp builds it, a graph of two layers: `relu(D x)` with `D = A - B`, then that
output plus `B x` as a residual of the input, so that each output is
`B x + relu((A - B) x) = max(A x, B x)` (`max_eq_add_relu_sub`). `A` and `B` select the two
operands of each pair (a window of a pooling layer, folded pairwise).

## Inputs
* `D` – the difference `A - B` of the operands' maps
* `B` – the second operand's map

## Output
* the network of the two layers
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def GraphNet.maxPool (D B : Mat ℝ m n) : GraphNet [n] m :=
  -- 1. relu(D x), from the input
  .layer ⟨⟨0, Nat.succ_pos _⟩, D, fun _ => 0, [], .elementwise relu⟩
    -- 2. that output, plus B x from the input
    (.layer ⟨⟨0, Nat.succ_pos _⟩, (1 : Mat ℝ m m), fun _ => 0, [⟨⟨1, Nat.lt_succ_self _⟩, B⟩],
      .identity⟩ .done)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
