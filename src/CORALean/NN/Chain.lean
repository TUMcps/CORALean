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

`eval` is the composite, which is what a network is sound at.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive Chain : ℕ → ℕ → Type where
  | nil {n : ℕ} : Chain n n
  | cons {n m k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) : Chain n k

/-- The composite, applied left to right as the layers are. -/
def Chain.eval : ∀ {n m : ℕ}, Chain n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons f rest, x => rest.eval (f x)

theorem Chain.eval_nil (x : Vec ℝ n) : (Chain.nil : Chain n n).eval x = x := rfl

theorem Chain.eval_cons {k : ℕ} (f : Vec ℝ n → Vec ℝ m) (rest : Chain m k) (x : Vec ℝ n) :
    (Chain.cons f rest).eval x = rest.eval (f x) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
