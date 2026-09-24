import CORALean.NN.Definitions.RefinableLayer

/-!
# The layer a pattern names

Reading one pattern off a refinable layer gives a plain `Layer`, which is the only thing a
network ever runs.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer a pattern names, which is the only thing a network ever runs. -/
def RefinableLayer.atPattern (L : RefinableLayer S n m) (t : OrderPattern n) : Layer S n m where
  enclose := L.enclose t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
