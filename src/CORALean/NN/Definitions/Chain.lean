import CORALean.NN.NeuralNetwork

/-!
# The functions a network's layers compute

`Layer` stores no function, so nothing reads a network's layer maps off it: the
exact function is a `Prop` and a `Prop` cannot be recursed over. A `Chain` is
that missing data — one function per layer, the dimensions chaining exactly as
a network's do — and it is where everything about the *exact* map lives: the
chain rule, sensitivity, a Lipschitz constant per layer.

It is a specification and never a computation, which is why it may store what
`Layer` may not. Nothing built here is ever run; `NeuralNetwork.Sound` at
`c.eval` is the only bridge back, and it is a proposition.
-/

-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive Chain : ℕ → ℕ → Type where
  | nil {n : ℕ} : Chain n n
  | cons {n m k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) : Chain n k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
