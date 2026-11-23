module

public import CORALean.NN.Definitions.GraphNetFloat

@[expose] public section

/-!
# `GraphNet.productSum`

MatMul as CORA.cpp lowers it, in floats: the layer `A x + a` with the product of the halves
(`productLine`'s parameters `p`, `τ`, `w₂`, `w₁`), then the sums `S`. Its outputs are the sums of
the products (`Real.GraphNet.productSum_eval`), enclosed by `GraphNet.productSum_encloses`.

## Inputs
* `A` – the factors' maps, the first factors over the second
* `a` – the factors' offsets
* `S` – the sums of the products
* `p` – the square root's Newton steps
* `τ` – the least scale
* `w₂` – the margin's factor of the centers' product
* `w₁` – the margin's factor of the larger end, at a generator count
* `slots` – whether the product's errors become generators

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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k n o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GraphNet.productSum (A : Mat 𝕋 (k + k) n) (a : Vec 𝕋 (k + k)) (S : Mat 𝕋 o (k + k)) (p : ℕ)
    (τ w₂ : 𝕋) (w₁ : ℕ → 𝕋) (slots : Bool) : GraphNet 𝕋 [n] o :=
  -- 1. the products of the factors A x + a
  .layer ⟨⟨0, Nat.succ_pos _⟩, A, a, [], .product k p τ w₂ w₁ slots⟩
    -- 2. their sums
    (.layer ⟨⟨0, Nat.succ_pos _⟩, S, fun _ => zero, [], .identity⟩ .done)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
