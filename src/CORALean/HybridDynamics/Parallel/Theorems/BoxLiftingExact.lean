module

public import CORALean.HybridDynamics.Parallel.Theorems.BoxLifting
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact

@[expose] public section

/-!
# `boxLifting` is exact

The product of the invariants, the product of the input boxes and the block-projection preimage of
a guard each contain exactly the stacks whose blocks lie in the components' sets, so `boxLifting`
meets `Lifting.Exact`, which the converse of `Run.toProduct` needs.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.boxLifting_exact (binds : ∀ i, Fin (n i) → InputSource k n m) :
    (ParallelHybridAutomaton.boxLifting binds).Exact where
  inv_inv gs x hx := by
    -- the lifted invariant is exactly the blocks'
    have hx' : stack x ∈ (HPolytope.stackProd gs).construct := hx
    rw [HPolytope.stackProd_exact] at hx'
    intro i
    have := hx' i
    rw [unstack_stack] at this
    exact this
  guard_inv i g x hx := by
    -- the lifted guard asks of a stack only that block `i` meet the guard
    have hx' : stack x ∈ (HPolytope.comap (blockProj i) g).construct := hx
    rw [HPolytope.comap_blockProj_exact] at hx'
    have : unstack (stack x) i ∈ g.construct := hx'
    rw [unstack_stack] at this
    exact this
  input_inv us v hv := by
    -- the product of the input sets is exactly the blocks'
    have hv' : stack (globalInput binds v) ∈ (Interval.stackProd us).construct := hv
    rw [Interval.stackProd_exact] at hv'
    intro i
    have := hv' i
    rw [unstack_stack] at this
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
