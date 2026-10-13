import CORALean.HybridDynamics.Parallel.Theorems.ZonoLifting
import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact

/-!
# `zonoLifting` is exact

The product of the invariants, the product of the input sets (`Zonotope.stackProd_exact`) and the
block-projection preimage of a guard each contain exactly the stacks whose blocks lie in the
components' sets, so `zonoLifting` meets `Lifting.Exact`.
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

theorem ParallelHybridAutomaton.zonoLifting_exact (binds : ∀ i, Fin (n i) → InputSource k n m) :
    (ParallelHybridAutomaton.zonoLifting binds).Exact where
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
    have hv' : stack (globalInput binds v) ∈ (Zonotope.stackProd us).construct := hv
    rw [Zonotope.stackProd_exact] at hv'
    intro i
    have := hv' i
    rw [unstack_stack] at this
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
