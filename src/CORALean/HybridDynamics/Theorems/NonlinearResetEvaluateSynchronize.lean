module

public import CORALean.HybridDynamics.Operations.NonlinearResetSynchronize
public import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate

@[expose] public section

/-!
# `NonlinearReset.synchronize` evaluates to the sum

The synchronized reset at a point is the sum of the component resets there, plus the pre-jump
value at the coordinates `idStates`: the statement of CORA's `synchronize`, exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.evaluate_synchronize (rs : Fin k → NonlinearReset n m n)
    (idStates : Finset (Fin n)) (x : Vec ℝ n) (u : Vec ℝ m) (i : Fin n) :
    (NonlinearReset.synchronize rs idStates).evaluate x u i =
      (if i ∈ idStates then x i else 0) + ∑ j, (rs j).evaluate x u i := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
