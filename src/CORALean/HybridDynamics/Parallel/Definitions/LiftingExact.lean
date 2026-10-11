import CORALean.HybridDynamics.Parallel.Definitions.Lifting

/-!
# A `Lifting` that loses nothing

`Lifting` asks only that the lifted sets contain what the components' sets put together: an outer
bargain, which is all `Run.toProduct` needs. The converse of `toProduct` needs the opposite
inclusions, and this structure is them: a point of a lifted set has the components' blocks in
the components' sets. The input set is read at the stack of `globalInput`, the only vectors a
parallel run feeds the product, as `Lifting.mem_input` is.

`boxLifting` satisfies it (`Theorems.BoxLiftingExact`): all three of its sets are exact.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {binds : ∀ i, Fin (n i) → InputSource k n m}


-- ========================================  MAIN TYPE  ========================================= --

structure ParallelHybridAutomaton.Lifting.Exact
    (lift : ParallelHybridAutomaton.Lifting S G n m binds) : Prop where
  inv_inv (gs : ∀ i, G (n i)) (x : ∀ i, Vec ℝ (n i)) (hx : stack x ∈ construct (lift.inv gs)) :
    ∀ i, x i ∈ construct (gs i)
  guard_inv (i : Fin k) (g : G (n i)) (x : ∀ i, Vec ℝ (n i))
    (hx : stack x ∈ construct (lift.guard i g)) : x i ∈ construct g
  input_inv (us : ∀ i, S (n i)) (v : ∀ i, Vec ℝ (n i))
    (hv : stack (globalInput binds v) ∈ construct (lift.input us)) :
    ∀ i, globalInput binds v i ∈ construct (us i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
