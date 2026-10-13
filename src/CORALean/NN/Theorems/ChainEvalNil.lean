module

public import CORALean.NN.Operations.ChainEval

@[expose] public section

/-!
# The empty chain is the identity

By definition; stated so that a rewrite can name it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.eval_nil (x : Vec ℝ n) : (Chain.nil : Chain n n).eval x = x := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
