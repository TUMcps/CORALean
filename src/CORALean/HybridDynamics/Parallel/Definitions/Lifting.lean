module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# Putting a component's set into the product's space

The product's invariant, input set and guards are sets in the *product* state space, built from
the components'. No representation here has a lift or a product (`ContSet` has neither), so the
caller supplies them, and this structure is what they owe: each is an outer bargain, containing
everything the components' sets put together say. A representation with a Cartesian product
and a preimage under a coordinate projection discharges it; nothing here says which.

`input` is read at the stack of inputs *with the state-bound coordinates zeroed*: those enter
the product through the matrix, and only the global ones are inputs of the product.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ParallelHybridAutomaton.Lifting (S G : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (n : Fin k → ℕ) (m : ℕ)
    (binds : ∀ i, Fin (n i) → InputSource k n m) where
  inv : (∀ i, G (n i)) → G (∑ i, n i)
  guard : ∀ i, G (n i) → G (∑ i, n i)
  input : (∀ i, S (n i)) → S (∑ i, n i)
  mem_inv (gs : ∀ i, G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : ∀ i, x i ∈ construct (gs i)) :
    stack x ∈ construct (inv gs)
  mem_guard (i : Fin k) (g : G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : x i ∈ construct g) :
    stack x ∈ construct (guard i g)
  mem_input (us : ∀ i, S (n i)) (v : ∀ i, Vec ℝ (n i))
    (hv : ∀ i, globalInput binds v i ∈ construct (us i)) :
    stack (globalInput binds v) ∈ construct (input us)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
