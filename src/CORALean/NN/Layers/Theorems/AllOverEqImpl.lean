module

public import CORALean.NN.Layers.Operations.AllOver

@[expose] public section

/-!
# `allOver` is the loop its implementation runs

The recursion peels one index per step and the loop folds from the last one, so the two agree by
induction on the length; the compiler is told to run the loop.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the recursive conjunction equals the loop
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

@[csimp] theorem allOver_eq_impl : -- --- CONCL ---
    @allOver = @step_allOverImpl := by -- --- PROOF ---
  funext k
  induction k with
  | zero => funext f; rw [step_allOverImpl, Fin.foldr_zero]; rfl
  | succ k ih =>
    funext f
    rw [step_allOverImpl, Fin.foldr_succ, ← step_allOverImpl, ← congrFun ih fun i => f i.succ]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
