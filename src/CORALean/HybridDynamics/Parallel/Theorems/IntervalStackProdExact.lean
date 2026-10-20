module

public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `Interval.stackProd` is the Cartesian product, exactly

A point of the stacked space is in the product of the boxes exactly when each of its blocks is in
its component's box. An equality, not an inclusion: this is the product `ContSet` lacks.

## Inputs
* `bs` – boxes of the components

## Hypotheses
* none

## Conclusion
* a point lies in the product iff each block lies in its component
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.stackProd_exact (bs : ∀ i, Interval (Vec ℝ (n i))) : -- --- CONCL ---
    (Interval.stackProd bs).construct =
      {z | ∀ i, unstack z i ∈ (bs i).construct} := by -- --- PROOF ---
  ext z
  constructor
  · -- a block's coordinate is a coordinate of the stack
    intro h i j
    have h' := h (finSigmaFinEquiv ⟨i, j⟩)
    change (stack fun i => (bs i).inf) (finSigmaFinEquiv ⟨i, j⟩) ≤ z (finSigmaFinEquiv ⟨i, j⟩) ∧
      z (finSigmaFinEquiv ⟨i, j⟩) ≤ (stack fun i => (bs i).sup) (finSigmaFinEquiv ⟨i, j⟩) at h'
    rw [stack_apply, stack_apply] at h'
    exact h'
  · -- every coordinate of the stack is some block's
    intro h p
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    have h' := h i j
    change (stack fun i => (bs i).inf) (finSigmaFinEquiv ⟨i, j⟩) ≤ z (finSigmaFinEquiv ⟨i, j⟩) ∧
      z (finSigmaFinEquiv ⟨i, j⟩) ≤ (stack fun i => (bs i).sup) (finSigmaFinEquiv ⟨i, j⟩)
    rw [stack_apply, stack_apply]
    exact h'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
