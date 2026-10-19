module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# Soundness of a network

The relational statement the reduction and refinement results need: the network encloses some
`f`, each layer some function of its own, which a reduced network satisfies for the function of
the network it was reduced from rather than for its own.
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
