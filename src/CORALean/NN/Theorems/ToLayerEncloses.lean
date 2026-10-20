module

public import CORALean.NN.Operations.ToLayer
public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# A sub-network is sound as a layer

`NeuralNetwork.toLayer` keeps only `enclose`, which is all a `Layer` holds, so
what the block computes has to be said separately — and it is the same
proposition at the same function, `enclose_outer` read at one layer instead of
a chain. That is what makes nesting free: a caller who has proved the
sub-network sound has proved the layer sound, with nothing left to check.

## Inputs
* `nn` – network
* `f` – map the network encloses

## Hypotheses
* `hf` – the network encloses the map

## Conclusion
* the network as a layer encloses the map
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.toLayer_encloses {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) : nn.toLayer.Encloses f :=
  ⟨hf.enclose_outer⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
