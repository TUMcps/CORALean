module

public import CORALean.NN.Operations.Backprop
public import CORALean.NN.Operations.ChainEval
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# CORA's `computeFGSMAttack`: one signed gradient step

`y = evaluate(x)`, `grad = backprop(lossDer(t, y))`, `z = x + ε .* sign(grad)`. The loss
derivative is an argument, as CORA's `lossDer` is (its default, `softmax(y) - t`, is the caller's
to pass); `idxLayer` is every layer. Real: the gradient is `Chain.backprop`'s.

## Inputs
* `c` – network chain
* `x` – input point
* `t` – target output
* `ε` – step size
* `lossDer` – derivative of the loss

## Output
* input point after one signed gradient step
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `computeFGSMAttack` at a target `t`: `z = x + ε .* sign(grad)`. -/
noncomputable def Chain.fgsmAttack (c : Chain n m) (x : Vec ℝ n) (t : Vec ℝ m) (ε : ℝ)
    (lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m) : Vec ℝ n :=
  let y := c.eval x
  let grad := c.backprop x (lossDer t y)
  fun i => x i + ε * Real.sign (grad i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
