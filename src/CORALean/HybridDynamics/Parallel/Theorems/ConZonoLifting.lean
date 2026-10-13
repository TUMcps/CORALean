import CORALean.HybridDynamics.Parallel.Theorems.ConZonotopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeComapBlockProjExact
import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
import CORALean.HybridDynamics.Parallel.Theorems.UnstackStack
import CORALean.HybridDynamics.Parallel.Definitions.Lifting
import CORALean.ContSet.HPolytope.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Instances

/-!
# `conZonoLifting`: a `Lifting` at constrained-zonotope inputs and halfspace descriptions

`boxLifting` with the input sets in `ConZonotope` instead of `Interval`: inputs in `ConZonotope`,
invariants and guards in `HPolytope`.

* `inv` and `guard` are `boxLifting`'s: `HPolytope.stackProd` and the block-projection preimage;
* `input` is `ConZonotope.stackProd`, the product of the components' input sets, exact
  (`Theorems.ConZonotopeStackProdExact`), not an outer enclosure; the `Lifting` fields ask only
  for the inclusion.

The invariant and the guard stay halfspace descriptions: a guard lifted to the product space is a
cylinder, unbounded in the other blocks, which no ConZonotope is. So this is the lifting for a
constrained-zonotope state or input set, with `HPolytope` where a set must be unbounded.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.conZonoLifting (binds : ∀ i, Fin (n i) → InputSource k n m) :
    ParallelHybridAutomaton.Lifting (fun n => ConZonotope (Vec ℝ n)) (fun n => HPolytope (Vec ℝ n))
      n m binds where
  inv := HPolytope.stackProd
  guard i g := HPolytope.comap (blockProj i) g
  input := ConZonotope.stackProd
  mem_inv gs x hx := by
    -- the product is exactly the blocks' sets, and the blocks of a stack are what was stacked
    show stack x ∈ (HPolytope.stackProd gs).construct
    rw [HPolytope.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hx i
  mem_guard i g x hx := by
    -- the lifted guard asks of a point only that its block `i` be in `g`
    show stack x ∈ (HPolytope.comap (blockProj i) g).construct
    rw [HPolytope.comap_blockProj_exact]
    show unstack (stack x) i ∈ g.construct
    rw [unstack_stack]
    exact hx
  mem_input us v hv := by
    -- as `mem_inv`, at the box of the stacked global inputs
    show stack (globalInput binds v) ∈ (ConZonotope.stackProd us).construct
    rw [ConZonotope.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hv i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
