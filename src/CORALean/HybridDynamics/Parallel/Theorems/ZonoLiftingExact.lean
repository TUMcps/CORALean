module

public import CORALean.HybridDynamics.Parallel.Operations.ZonoLifting
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVecOfDistinct

@[expose] public section

/-!
# `zonoLifting` is exact

The product of the invariants, the product of the disturbance sets (`Zonotope.stackProd_exact`) and
the block-projection preimage of a guard each contain exactly the stacks whose blocks lie in the
components' sets. The input set is the image of the product of the components' input sets under
`selectGlobal`: a point of it is the image of a stacked point, whose blocks are points of the
components' sets, and where each global input feeds one input those blocks agree with it
(`selectGlobal_mulVec_of_distinct`). So `zonoLifting` meets `Lifting.IsExact`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the zonotope lifting is exact
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet Matrix

variable {k m : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.zonoLifting_isExact :
    (ParallelHybridAutomaton.zonoLifting (k := k) (n := n) (m := m)).IsExact where
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
  input_inv b hb us _ g hg := by
    -- `g` is the image of a stacked point of the product, whose blocks agree with it
    have hg' : g ∈ (Zonotope.mtimes (selectGlobal b) (Zonotope.stackProd us)).construct := hg
    rw [← Zonotope.mtimes_exact] at hg'
    obtain ⟨z, hz, rfl⟩ := hg'
    rw [Zonotope.stackProd_exact] at hz
    intro i
    refine ⟨unstack z i, hz i, fun j a hj => ?_⟩
    show _ = (selectGlobal b *ᵥ z) a
    rw [selectGlobal_mulVec_of_distinct hb z hj]
    rfl
  dist_inv ws w hw := by
    -- the product of the disturbance sets is exactly the blocks'
    have hw' : stack w ∈ (Zonotope.stackProd ws).construct := hw
    rw [Zonotope.stackProd_exact] at hw'
    intro i
    have := hw' i
    rw [unstack_stack] at this
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
