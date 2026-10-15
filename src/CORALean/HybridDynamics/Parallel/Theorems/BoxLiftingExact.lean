module

public import CORALean.HybridDynamics.Parallel.Operations.BoxLifting
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVecOfDistinct

@[expose] public section

/-!
# `boxLifting` is exact

The product of the invariants, the product of the disturbance boxes and the block-projection
preimage of a guard each contain exactly the stacks whose blocks lie in the components' sets.
The box of the global inputs bounds `a` by the box of the one input bound to it, where each global
input feeds one input; a point of each component's box, its globally bound coordinates replaced by
the global inputs', is then in that box. So `boxLifting` meets `Lifting.Exact`, the components'
boxes being nonempty.
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

theorem ParallelHybridAutomaton.boxLifting_exact :
    (ParallelHybridAutomaton.boxLifting (k := k) (n := n) (m := m)).Exact where
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
  input_inv b hb us hne g hg := by
    -- a point of the box, its globally bound coordinates the global inputs'
    intro i
    obtain ⟨p, hp⟩ := hne i
    have hv : ∀ j, (us i).inf j ≤ (match b i j with
        | .global a => g a
        | .output _ _ => p j) ∧ (match b i j with
        | .global a => g a
        | .output _ _ => p j) ≤ (us i).sup j := by
      intro j
      cases hj : b i j with
      | global a =>
        -- the global input's bounds are those of the one input bound to it
        have h := hg a
        change (selectGlobal b *ᵥ _) a ≤ g a ∧ g a ≤ (selectGlobal b *ᵥ _) a at h
        rw [selectGlobal_mulVec_of_distinct hb _ hj, selectGlobal_mulVec_of_distinct hb _ hj,
          stack_apply, stack_apply] at h
        exact h
      | output c s => exact hp j
    exact ⟨fun j => match b i j with
      | .global a => g a
      | .output _ _ => p j, hv, fun j a hj => by simp only [hj]⟩
  dist_inv ws w hw := by
    -- the product of the disturbance sets is exactly the blocks'
    have hw' : stack w ∈ (Interval.stackProd ws).construct := hw
    rw [Interval.stackProd_exact] at hw'
    intro i
    have := hw' i
    rw [unstack_stack] at this
    exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
