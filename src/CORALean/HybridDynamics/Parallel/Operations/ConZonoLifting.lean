module

public import CORALean.HybridDynamics.Parallel.Theorems.ConZonotopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVecStack
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Instances

@[expose] public section

/-!
# `conZonoLifting`: a `Lifting` at constrained-zonotope inputs and halfspace descriptions

`boxLifting` with the input and disturbance sets in `ConZonotope` instead of `Interval`. `inv` and
`guard` are `boxLifting`'s; `input b` is the image of `ConZonotope.stackProd` under
`selectGlobal b`; `dist` is `ConZonotope.stackProd`, exact (`Theorems.ConZonotopeStackProdExact`).
The invariant and the guard stay halfspace descriptions: a guard lifted to the product space is a
cylinder, unbounded in the other blocks, which no ConZonotope is.

## Inputs
* none

## Output
* lifting at constrained zonotope inputs
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.conZonoLifting :
    ParallelHybridAutomaton.Lifting (𝒞) (ℋ𝒫) n m where
  inv := HPolytope.stackProd
  guard i g := HPolytope.comap (blockProj i) g
  input b us := ConZonotope.mtimes (selectGlobal b) (ConZonotope.stackProd us)
  dist := ConZonotope.stackProd
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
  mem_input b us g hg hz := by
    -- the components' points, stacked, are in the product, and `selectGlobal` takes them to `g`
    choose v hv hva using hg
    show g ∈ (ConZonotope.mtimes (selectGlobal b) (ConZonotope.stackProd us)).construct
    rw [← ConZonotope.mtimes_exact, ← selectGlobal_mulVec_stack b v g hva hz]
    refine ⟨stack v, ?_, rfl⟩
    rw [ConZonotope.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hv i
  mem_dist ws w hw := by
    -- as `mem_inv`, at the product of the disturbance sets
    show stack w ∈ (ConZonotope.stackProd ws).construct
    rw [ConZonotope.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hw i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
