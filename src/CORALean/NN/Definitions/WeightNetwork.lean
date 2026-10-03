import CORALean.NN.Definitions.WeightLayer

/-!
# A network of weight layers

`neuralNetwork` as `getNormalForm` sees it: weight layers applied first to last, the dimensions
chaining so that a network is well-formed by construction.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- Layers applied first to last. -/
inductive WeightNetwork (α : Type) : ℕ → ℕ → Type where
  | nil {n : ℕ} : WeightNetwork α n n
  | cons {n m k : ℕ} (L : WeightLayer α n m) (rest : WeightNetwork α m k) : WeightNetwork α n k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
