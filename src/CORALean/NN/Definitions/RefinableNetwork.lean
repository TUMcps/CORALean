module

public import CORALean.NN.Definitions.RefinableLayer

@[expose] public section

/-!
# A network whose layers can each be refined

`NeuralNetwork` with a `RefinableLayer` at every node: the same chain, the same
dimensions chaining, and one level per layer still to be chosen. Reading a
schedule off it gives a `NeuralNetwork` back, so nothing downstream — `enclose`,
its enclosure, `Specification` — knows a refinement loop exists.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A chain of refinable layers, the dimensions chaining. -/
inductive RefinableNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type where
  | nil {n : ℕ} : RefinableNetwork S n n
  | cons {n m k : ℕ} (L : RefinableLayer S n m) (rest : RefinableNetwork S m k) :
      RefinableNetwork S n k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
