module

public import CORALean.NN.Operations.Eval

@[expose] public section

/-!
# A network is sound at what it computes

Each layer is sound at its own `eval` by `Enclose.toLayer_sound`, and `eval` composes them
exactly as `Sound` does, so the relation holds at `eval` with no hypothesis. Every
hypothesis-free statement about a network is the relational one read here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.sound_eval : ∀ {n m : ℕ} (nn : NeuralNetwork S n m), nn.Sound nn.eval.out
  | _, _, .output => .output fun x => by simp [NeuralNetwork.eval]
  | _, _, .layer (inst := _) curr tail =>
      .layer (Enclose.toLayer_sound curr) (NeuralNetwork.sound_eval tail)
        fun x => by simp [NeuralNetwork.eval]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
