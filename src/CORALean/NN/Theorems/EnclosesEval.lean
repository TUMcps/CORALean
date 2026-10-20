module

public import CORALean.NN.Definitions.Encloses
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Operations.Eval

@[expose] public section

/-!
# A network is sound at what it computes

Each layer is sound at its own `eval` by `Enclose.toLayer_encloses`, and `eval` composes them
exactly as `Sound` does, so the relation holds at `eval` with no hypothesis. Every
hypothesis-free statement about a network is the relational one read here.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* every network encloses the map it computes
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.encloses_eval :
    ∀ {n m : ℕ} (nn : NeuralNetwork S n m), nn.Encloses nn.eval.out
  | _, _, .output => .output fun x => by simp [NeuralNetwork.eval]
  | _, _, .layer (inst := _) curr tail =>
      .layer (Enclose.toLayer_encloses curr) (NeuralNetwork.encloses_eval tail)
        fun x => by simp [NeuralNetwork.eval]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
