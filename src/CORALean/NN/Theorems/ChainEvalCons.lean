import CORALean.NN.Operations.ChainEval

/-!
# A chain's composite, one layer in

The head map first, then the rest's composite, by definition; stated so that a rewrite can name
it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.eval_cons {k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) (x : Vec ℝ n) :
    (Chain.cons f rest).eval x = rest.eval (f x) := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
