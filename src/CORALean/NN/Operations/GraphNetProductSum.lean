module

public import CORALean.NN.Definitions.GraphNet

@[expose] public section

/-!
# `GraphNet.productSum`

MatMul of two values as CORA.cpp lowers it: the layer `y = A x + a` with the product activation
`[y_a; y_b] ↦ [y_a ⊙ y_b; 0]`, then the sums `S` of the products. Row `i` of `A`'s first half and
row `i` of its second are the two factors of product `i`; for `C = P Q`, product `(r, s, t)` is
`P_rt Q_ts` and `S` sums over `t`.

## Inputs
* `A` – the factors' maps, the first factors over the second
* `a` – the factors' offsets
* `S` – the sums of the products

## Output
* the network of the two layers
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k n o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def GraphNet.productSum (A : Mat ℝ (k + k) n) (a : Vec ℝ (k + k))
    (S : Mat ℝ o (k + k)) : GraphNet [n] o :=
  -- 1. the products of the factors A x + a
  .layer ⟨⟨0, Nat.succ_pos _⟩, A, a, [], .product k⟩
    -- 2. their sums
    (.layer ⟨⟨0, Nat.succ_pos _⟩, S, fun _ => 0, [], .identity⟩ .done)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
