module

public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# Neural networks: the computation graph

CORA's `neuralNetwork`: layers applied one after another, first layer first, the dimensions
chaining so that a network is well-formed by construction. `output` ends the chain, and
`layer curr tail` puts one layer of any `Enclose` kind in front of the rest: the kinds mix
freely, the instance travelling with each layer. Storing the kind puts `NeuralNetwork` in
`Type 1`; a network is itself an `Enclose` kind, and nests into another through
`Enclose.pack`, which forgets the kind in `Type`.

A chain rather than a node-and-edge graph, and that is not a restriction: a branch widens the
vector and carries the branched coordinates along — `IdentityLayer` on that block, a linear
layer to route or duplicate — so every value stays in one set and the dependency survives.

What a network computes is its layers' `eval`s composed, `NeuralNetwork.eval`. `Sound` is the
weaker, relational statement the reduction and refinement results need: the network encloses
some `f`, each layer some function of its own, which a reduced network satisfies for the
function of the network it was reduced from rather than for its own.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive NeuralNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type 1 where
  | output {n : ℕ} : NeuralNetwork S n n
  | layer {n m k : ℕ} {L : ℕ → ℕ → Type} [inst : Enclose L S] (curr : L n m)
      (tail : NeuralNetwork S m k) : NeuralNetwork S n k

/-- That the network encloses `f`, as a relation: each layer sound at some function of its
own, and `f` their composite, whichever functions those are. -/
inductive NeuralNetwork.Sound :
    ∀ {n m : ℕ}, NeuralNetwork S n m → (Vec ℝ n → Vec ℝ m) → Prop where
  | output {n : ℕ} {f : Vec ℝ n → Vec ℝ n} (hf : ∀ x, f x = x) :
      NeuralNetwork.Sound (.output : NeuralNetwork S n n) f
  | layer {n m k : ℕ} {L : ℕ → ℕ → Type} [inst : Enclose L S] {curr : L n m}
      {tail : NeuralNetwork S m k} {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k}
      {f : Vec ℝ n → Vec ℝ k} (hL : (Enclose.toLayer (S := S) curr).Sound g)
      (htail : tail.Sound h) (hf : ∀ x, f x = h (g x)) :
      NeuralNetwork.Sound (.layer curr tail) f

/-- The identity at `output`, which is the constructor read at `f = id`. -/
theorem NeuralNetwork.sound_output : (NeuralNetwork.output : NeuralNetwork S n n).Sound id :=
  .output fun _ => rfl

/-- Composition at `layer`, which is the constructor read at `f = h ∘ g`. -/
theorem NeuralNetwork.sound_layer {L : ℕ → ℕ → Type} [Enclose L S] {curr : L n m}
    {tail : NeuralNetwork S m k} {g : Vec ℝ n → Vec ℝ m} {h : Vec ℝ m → Vec ℝ k}
    (hL : (Enclose.toLayer (S := S) curr).Sound g) (htail : tail.Sound h) :
    (NeuralNetwork.layer curr tail).Sound (h ∘ g) :=
  .layer hL htail fun _ => rfl

/-- Soundness is stable under replacing the function by one that agrees with it
everywhere, which is what lets a caller name the composite in its own terms. -/
theorem NeuralNetwork.Sound.congr {nn : NeuralNetwork S n m} {f f' : Vec ℝ n → Vec ℝ m}
    (h : nn.Sound f) (hff : ∀ x, f' x = f x) : nn.Sound f' := by
  induction h with
  | output hf => exact .output fun x => by rw [hff x, hf x]
  | layer hL htail hf _ => exact .layer hL htail fun x => by rw [hff x, hf x]

/-- One layer, so that a single layer needs no special case anywhere. -/
def NeuralNetwork.ofLayer {L : ℕ → ℕ → Type} [Enclose L S] (curr : L n m) :
    NeuralNetwork S n m :=
  .layer curr .output

theorem NeuralNetwork.ofLayer_sound {L : ℕ → ℕ → Type} [Enclose L S] {curr : L n m}
    {f : Vec ℝ n → Vec ℝ m} (h : (Enclose.toLayer (S := S) curr).Sound f) :
    (NeuralNetwork.ofLayer (S := S) curr).Sound f :=
  .layer h (.output fun _ => rfl) fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
