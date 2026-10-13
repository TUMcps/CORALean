module

public import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeComapBlockProjExact
public import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProd
public import CORALean.HybridDynamics.Parallel.Theorems.UnstackStack
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.ContSet.HPolytope.Real.Instances

@[expose] public section

/-!
# `boxLifting`: a `Lifting` at boxes and halfspace descriptions

The first concrete `Lifting`: inputs in `Interval`, invariants and guards in `HPolytope`.

* `inv` is `HPolytope.stackProd`, the Cartesian product of the components' invariants;
* `guard i g` is `HPolytope.comap (blockProj i) g`, constraining block `i` and free elsewhere,
  which no box can say;
* `input` is `Interval.stackProd`, the product of the components' input sets. The state-bound
  coordinates are zero in `globalInput`, so a component's `U` must contain `0` there for a stay
  to exist at all, and the product's box then contains the stacked zero too.

All three are exact (`Theorems.IntervalStackProdExact`, `Theorems.HPolytopeStackProdExact`), not
outer enclosures; the `Lifting` fields ask only for the inclusion.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.boxLifting (binds : ∀ i, Fin (n i) → InputSource k n m) :
    ParallelHybridAutomaton.Lifting (fun n => Interval (Vec ℝ n)) (fun n => HPolytope (Vec ℝ n))
      n m binds where
  inv := HPolytope.stackProd
  guard i g := HPolytope.comap (blockProj i) g
  input := Interval.stackProd
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
    show stack (globalInput binds v) ∈ (Interval.stackProd us).construct
    rw [Interval.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hv i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
