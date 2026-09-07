import CORALean.NN.Layer

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, the dimensions
chaining so that a network is well-formed by construction and `eval` needs no
side condition.

A chain rather than a node-and-edge graph, and that is not a restriction. A
layer is any function with an enclosure, so a branch is expressed by widening
the vector and carrying the branched coordinates along — `Layer.identity` on
that block, a linear layer to route or to duplicate, and the two paths rejoined
by another. That keeps every value in one set, so the dependency between the
branches survives; splitting into two sets and recombining them would lose it,
which is precisely the precision a skip connection is there to preserve.

`image` is what verification is about and what nothing computes: the exact
image, which `enclose` encloses. It is `enclose`'s own recursion, run over
sets rather than representations, so soundness is one induction relating the
two instead of one that re-derives the image of a composition at every step.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive NeuralNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type where
  | nil {n : ℕ} : NeuralNetwork S n n
  | cons {n m k : ℕ} (L : Layer S n m) (rest : NeuralNetwork S m k) : NeuralNetwork S n k

def NeuralNetwork.eval : ∀ {n m : ℕ}, NeuralNetwork S n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

/-- The exact image a network produces: not computable, and what `enclose`
encloses. `enclose`'s own recursion, run over sets instead of representations. -/
def NeuralNetwork.image : ∀ {n m : ℕ}, NeuralNetwork S n m → Set (Vec ℝ n) → Set (Vec ℝ m)
  | _, _, .nil, X => X
  | _, _, .cons L rest, X => rest.image (L.image X)

theorem NeuralNetwork.image_nil (X : Set (Vec ℝ n)) :
    (NeuralNetwork.nil : NeuralNetwork S n n).image X = X := rfl

theorem NeuralNetwork.image_cons (L : Layer S n m) (rest : NeuralNetwork S m k)
    (X : Set (Vec ℝ n)) : (NeuralNetwork.cons L rest).image X = rest.image (L.image X) := rfl

/-- `image` agrees with mapping `eval` over the set — the recursion and the
alias it replaces, tied together in one induction. -/
theorem NeuralNetwork.image_eq_eval_image :
    ∀ {n m : ℕ} (nn : NeuralNetwork S n m) (X : Set (Vec ℝ n)), nn.image X = nn.eval '' X
  | _, _, .nil, X => (Set.image_id' X).symm
  | _, _, .cons L rest, X => by
      rw [NeuralNetwork.image_cons, rest.image_eq_eval_image]
      exact Set.image_image rest.eval L.eval X

/-- One layer, so that a single layer needs no special case anywhere. -/
def NeuralNetwork.ofLayer (L : Layer S n m) : NeuralNetwork S n m := .cons L .nil

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
