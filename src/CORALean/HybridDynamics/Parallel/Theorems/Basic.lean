module

public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj

@[expose] public section

/-!
# `HybridDynamics/Parallel/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- ====================================  `blockProj_apply`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `blockProj c` applied to a point is its block `c`, by definition. -/
@[simp] theorem blockProj_apply (c : Fin k) (z : Vec ℝ (∑ i, n i)) :
    blockProj c z = unstack z c := rfl


-- ======================================  `stack_apply`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Coordinate `⟨i, j⟩` of the stack is coordinate `j` of block `i`. -/
@[simp] theorem stack_apply (x : ∀ i, Vec ℝ (n i)) (i : Fin k) (j : Fin (n i)) :
    stack x (finSigmaFinEquiv ⟨i, j⟩) = x i j := by
  unfold stack
  rw [Equiv.symm_apply_apply]


-- =====================================  `unstack_stack`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The blocks of a stack are what was stacked. `Theorems.StackUnstack` is the other way round. -/
@[simp] theorem unstack_stack (x : ∀ i, Vec ℝ (n i)) : unstack (stack x) = x := by
  funext i j
  unfold unstack stack
  rw [Equiv.symm_apply_apply]

end CORALean


namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- ============================  `HPolytope.comap_blockProj_exact`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The preimage of a component's guard under the projection onto its block: a constraint on that
block and free elsewhere, which no box can say. `HPolytope.comap_exact` at `blockProj`. -/
theorem HPolytope.comap_blockProj_exact (c : Fin k) (g : HPolytope (Vec ℝ (n c))) :
    (HPolytope.comap (blockProj c) g).construct = {z | unstack z c ∈ g.construct} :=
  HPolytope.comap_exact _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
