module

public import CORALean.HybridDynamics.Parallel.Operations.ConZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdValue
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack

@[expose] public section

/-!
# `ConZonotope.stackProd` is exact

A point is in the stacked constrained zonotope exactly when each block is in its component's:
the generators' blocks are independent (`Zonotope.stackProd_value`) and so are the constraints on
the coefficients (`HPolytope.stackProd_exact`). An equality, not an enclosure.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.stackProd_exact (zs : ∀ i, ConZonotope (Vec ℝ (n i))) :
    (ConZonotope.stackProd zs).construct =
      {z | ∀ i, unstack z i ∈ (zs i).construct} := by -- --- PROOF ---
  classical
  -- the underlying zonotopes, whose stack carries the generators
  let Zs : ∀ i, Zonotope (Vec ℝ (n i)) := fun i => ⟨(zs i).h, (zs i).c, (zs i).G⟩
  have hval : ∀ (β : Fin (∑ i, (zs i).h) → ℝ) (i : Fin k),
      unstack ((ConZonotope.stackProd zs).c +
        ∑ p : Fin (∑ i, (zs i).h), β p • (ConZonotope.stackProd zs).G p) i =
        (zs i).c + ∑ j, β (finSigmaFinEquiv (n := fun i => (zs i).h) ⟨i, j⟩) • (zs i).G j :=
    fun β i => Zonotope.stackProd_value Zs β i
  ext z
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩ i
    -- the constraints hold block by block, and the block's value is the component's own
    have hP' : β ∈ (HPolytope.stackProd fun i => (zs i).P).construct := hP
    rw [HPolytope.stackProd_exact] at hP'
    exact ⟨unstack β i, fun j => hβ _, hP' i, hval β i⟩
  · intro h
    choose βf hβ hP hz using h
    -- the coefficients of all components, stacked
    let β : Vec ℝ (∑ i, (zs i).h) := stack βf
    have hβi : ∀ (i : Fin k) (j : Fin (zs i).h),
        β (finSigmaFinEquiv (n := fun i => (zs i).h) ⟨i, j⟩) = βf i j :=
      fun i j => stack_apply βf i j
    -- the bound, the constraint and the value, each from the blocks'
    refine ⟨β, fun p => ?_, ?_, ?_⟩
    · obtain ⟨⟨i, j⟩, rfl⟩ := (finSigmaFinEquiv (n := fun i => (zs i).h)).surjective p
      rw [hβi]
      exact hβ i j
    · -- the constraint holds on each block
      show β ∈ (HPolytope.stackProd fun i => (zs i).P).construct
      rw [HPolytope.stackProd_exact]
      intro i
      show unstack (stack βf) i ∈ _
      rw [unstack_stack]
      exact hP i
    · -- both sides have the same blocks
      show z = (ConZonotope.stackProd zs).c +
        ∑ p : Fin (∑ i, (zs i).h), β p • (ConZonotope.stackProd zs).G p
      have hu : unstack ((ConZonotope.stackProd zs).c +
          ∑ p : Fin (∑ i, (zs i).h), β p • (ConZonotope.stackProd zs).G p) = unstack z := by
        funext i
        rw [hval β i, hz i]
        simp only [hβi]
      calc z = stack (unstack z) := (stack_unstack z).symm
        _ = stack (unstack ((ConZonotope.stackProd zs).c +
            ∑ p : Fin (∑ i, (zs i).h), β p • (ConZonotope.stackProd zs).G p)) := by rw [hu]
        _ = _ := stack_unstack _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
