import CORALean.HybridDynamics.Parallel.Theorems.ConZonoLifting
import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact

/-!
# `conZonoLifting` is exact

The product of the invariants, the product of the input sets (`ConZonotope.stackProd_exact`) and the
block-projection preimage of a guard each contain exactly the stacks whose blocks lie in the
components' sets, so `conZonoLifting` meets `Lifting.Exact`.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.conZonoLifting_exact (binds : ∀ i, Fin (n i) → InputSource k n m) :
    (ParallelHybridAutomaton.conZonoLifting binds).Exact where
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
    have hv' : stack (globalInput binds v) ∈ (ConZonotope.stackProd us).construct := hv
    rw [ConZonotope.stackProd_exact] at hv'
    intro i
    have := hv' i
    rw [unstack_stack] at this
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
