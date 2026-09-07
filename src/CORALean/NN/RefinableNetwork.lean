import CORALean.NN.RefinableLayer

/-!
# A network whose layers can each be refined

`NeuralNetwork` with a `RefinableLayer` at every node: the same chain, the same
dimensions chaining, and one level per layer still to be chosen. Reading a
schedule off it gives a `NeuralNetwork` back, so nothing downstream — `enclose`,
its enclosure, `Specification` — knows a refinement loop exists.

`eval` is defined here and not read off a schedule, which is the point of
`RefinableLayer` keeping `eval` outside `enclose`: the exact image is one
set, fixed before any level is chosen, and every schedule encloses that same set.

`length` is what a heuristic ranks over — a schedule is an infinite sequence and
only its first `length` entries are ever read.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

inductive RefinableNetwork (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] : ℕ → ℕ → Type where
  | nil {n : ℕ} : RefinableNetwork S n n
  | cons {n m k : ℕ} (L : RefinableLayer S n m) (rest : RefinableNetwork S m k) :
      RefinableNetwork S n k

def RefinableNetwork.eval : ∀ {n m : ℕ}, RefinableNetwork S n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

/-- The exact image the whole loop is about: fixed before a level is chosen, so
every schedule encloses it. -/
def RefinableNetwork.image (rn : RefinableNetwork S n m) (X : Set (Vec ℝ n)) : Set (Vec ℝ m) :=
  rn.eval '' X

/-- How many levels a schedule is read at. -/
def RefinableNetwork.length : ∀ {n m : ℕ}, RefinableNetwork S n m → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ rest => rest.length + 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
