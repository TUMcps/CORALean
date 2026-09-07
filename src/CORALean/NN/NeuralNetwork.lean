import CORALean.NN.Layer

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, the dimensions
chaining so that a network is well-formed by construction and nothing needs a
side condition.

A chain rather than a node-and-edge graph, and that is not a restriction. A
layer is any function with an enclosure, so a branch is expressed by widening
the vector and carrying the branched coordinates along — `Layer.identity` on
that block, a linear layer to route or to duplicate, and the two paths rejoined
by another. That keeps every value in one set, so the dependency between the
branches survives.

The network holds `Layer`s, which store no function, so a network of float
layers is a plain `def`. What it computes is said by `Sound`, one `Prop` per
constructor: `nil` is the identity and `cons` composes. The exact image is then
`f '' X` for any `f` the network is sound at, and nothing computes it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: 07-September-2026


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive NeuralNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type where
  | nil {n : ℕ} : NeuralNetwork S n n
  | cons {n m k : ℕ} (L : Layer S n m) (rest : NeuralNetwork S m k) : NeuralNetwork S n k

/-- What a network computes, as a relation rather than a field: the layers'
own obligations, chained in the order `enclose` applies them. -/
inductive NeuralNetwork.Sound :
    ∀ {n m : ℕ}, NeuralNetwork S n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | nil {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) :
      NeuralNetwork.Sound (.nil : NeuralNetwork S n n) f
  | cons {n m k : ℕ} {L : Layer S n m} {rest : NeuralNetwork S m k}
      {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k} {f : Vec ℝ n → Vec ℝ k}
      (hL : L.Sound g) (hrest : rest.Sound h) (hf : ∀ x, f x = h (g x)) :
      NeuralNetwork.Sound (.cons L rest) f

/-- The identity at `nil`, which is the constructor read at `f = id`. -/
theorem NeuralNetwork.sound_nil : (NeuralNetwork.nil : NeuralNetwork S n n).Sound id :=
  .nil fun _ => rfl

/-- Composition at `cons`, which is the constructor read at `f = h ∘ g`. -/
theorem NeuralNetwork.sound_cons {L : Layer S n m} {rest : NeuralNetwork S m k}
    {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k} (hL : L.Sound g) (hrest : rest.Sound h) :
    (NeuralNetwork.cons L rest).Sound (h ∘ g) :=
  .cons hL hrest fun _ => rfl

/-- Soundness is stable under replacing the function by one that agrees with it
everywhere, which is what lets a caller name the composite in its own terms. -/
theorem NeuralNetwork.Sound.congr {nn : NeuralNetwork S n m} {f f' : Vec ℝ n → Vec ℝ m}
    (h : nn.Sound f) (hff : ∀ x, f' x = f x) : nn.Sound f' := by
  induction h with
  | nil hf => exact .nil fun x => by rw [hff x, hf x]
  | cons hL hrest hf _ => exact .cons hL hrest fun x => by rw [hff x, hf x]

/-- One layer, so that a single layer needs no special case anywhere. -/
def NeuralNetwork.ofLayer (L : Layer S n m) : NeuralNetwork S n m := .cons L .nil

theorem NeuralNetwork.ofLayer_sound {L : Layer S n m} {f : Vec ℝ n → Vec ℝ m} (h : L.Sound f) :
    (NeuralNetwork.ofLayer L).Sound f :=
  .cons h (.nil fun _ => rfl) fun _ => rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
