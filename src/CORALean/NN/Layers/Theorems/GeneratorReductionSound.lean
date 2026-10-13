module

public import CORALean.NN.Layers.Operations.GeneratorReduction

@[expose] public section

/-!
# What the generator reduction layer encloses

The identity: `reduce_outer` says the reduced set contains the set, whichever generators are
dropped.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.generatorReduction_sound [∀ n, Reduce (S n) (Vec ℝ n)] (n maxGens : ℕ) :
    (Layer.generatorReduction (S := S) n maxGens).Sound id :=
  ⟨fun s _x hx => Reduce.reduce_outer s maxGens hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
