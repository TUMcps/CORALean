import CORALean.NN.Operations.ChainEval

/-!
# The empty chain is the identity

By definition; stated so that a rewrite can name it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.eval_nil (x : Vec ℝ n) : (Chain.nil : Chain n n).eval x = x := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
