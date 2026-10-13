module

public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# What a network computes

Its layers' `eval`s composed, first layer first, inside `Erased` as each of them is: the
composite is built from `Erased.out`, which is noncomputable, but `Erased.mk` erases its
argument before anything is compiled, so a network of float layers still runs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NeuralNetwork.eval : ∀ {n m : ℕ}, NeuralNetwork S n m → Erased (Vec ℝ n → Vec ℝ m)
  | _, _, .output => Erased.mk id
  | _, _, .layer (inst := _) curr tail =>
      Erased.mk (tail.eval.out ∘ (Enclose.eval (S := S) curr).out)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
