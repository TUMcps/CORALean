module

public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# Putting a component's set into the product's space

The product's invariant and guards are sets in the product state space, its input set one in the
space of the global inputs and its disturbance set one in the stacked disturbance space, all built
from the components'. No representation here has a lift or a product, so the caller supplies them,
and this structure is what they owe: each is an outer bargain. `input b` is CORA's
`aux_mergeInputSet`: every vector of global inputs whose coordinates fed to each component `i` are
those of a point of `us i`, zero at the global inputs nothing reads. `dist` is CORA's
`aux_mergeDistNoiseSet`, the product of the components' disturbance sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- What a caller owes to lift the components' sets into the product space: the invariant, the
guards, the input set and the disturbance set, each as a set containing what the components' sets
put together. -/
structure ParallelHybridAutomaton.Lifting (S G : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (n : Fin k → ℕ) (m : ℕ) where
  inv : (∀ i, G (n i)) → G (∑ i, n i)
  guard : ∀ i, G (n i) → G (∑ i, n i)
  input {d q : Fin k → ℕ} : (∀ i, Fin (d i) → ResolveSource k q m) → (∀ i, S (d i)) → S m
  dist {d : Fin k → ℕ} : (∀ i, S (d i)) → S (∑ i, d i)
  mem_inv (gs : ∀ i, G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : ∀ i, x i ∈ construct (gs i)) :
    stack x ∈ construct (inv gs)
  mem_guard (i : Fin k) (g : G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : x i ∈ construct g) :
    stack x ∈ construct (guard i g)
  mem_input {d q : Fin k → ℕ} (b : ∀ i, Fin (d i) → ResolveSource k q m) (us : ∀ i, S (d i))
    (g : Vec ℝ m) (hg : ∀ i, ∃ v ∈ construct (us i), ∀ j a, b i j = .global a → v j = g a)
    (hz : ∀ a, (∀ i j, b i j ≠ .global a) → g a = 0) : g ∈ construct (input b us)
  mem_dist {d : Fin k → ℕ} (ws : ∀ i, S (d i)) (w : ∀ i, Vec ℝ (d i))
    (hw : ∀ i, w i ∈ construct (ws i)) : stack w ∈ construct (dist ws)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
