module

public import CORALean.HybridDynamics.Parallel.Theorems.ZonotopeStackProdValue
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack

@[expose] public section

/-!
# `Zonotope.stackProd` is exact

A point is in the stacked zonotope exactly when each of its blocks is in its component's zonotope:
the coefficients of different components' generators are independent, so a block's coefficients
can be chosen on their own. An equality, not an enclosure, as `IntervalStackProdExact` and
`HPolytopeStackProdExact` are for the other two stacked sets.

## Inputs
* `zs` – zonotopes of the components

## Hypotheses
* none

## Conclusion
* a point lies in the product iff each block lies in its component
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.stackProd_exact (zs : ∀ i, Zonotope (Vec ℝ (n i))) : -- --- CONCL ---
    (Zonotope.stackProd zs).construct =
      {z | ∀ i, unstack z i ∈ (zs i).construct} := by -- --- PROOF ---
  classical
  ext z
  constructor
  · -- a point of the stack has its block `i` at the coefficients of block `i`
    rintro ⟨β, hβ, rfl⟩ i
    refine ⟨fun j => β (finSigmaFinEquiv (n := fun i => (zs i).h) ⟨i, j⟩), fun j => hβ _, ?_⟩
    exact Zonotope.stackProd_value zs β i
  · intro h
    choose βf hβ hz using h
    -- the coefficients of block `i` are those chosen for component `i`
    let β : Fin (∑ i, (zs i).h) → ℝ := fun p =>
      (fun q : (Σ i, Fin (zs i).h) => βf q.1 q.2)
        ((finSigmaFinEquiv (n := fun i => (zs i).h)).symm p)
    have hβi : ∀ (i : Fin k) (j : Fin (zs i).h),
        β (finSigmaFinEquiv (n := fun i => (zs i).h) ⟨i, j⟩) = βf i j := by
      intro i j
      have key : ∀ q : (Σ i, Fin (zs i).h), q = ⟨i, j⟩ → βf q.1 q.2 = βf i j := by
        rintro q rfl; rfl
      exact key _ (Equiv.symm_apply_apply _ _)
    -- the stacked point has every block at its chosen coefficients, so equals `z`
    refine ⟨β, fun p => hβ _ _, ?_⟩
    show z = (Zonotope.stackProd zs).c +
      ∑ p : Fin (∑ i, (zs i).h), β p • (Zonotope.stackProd zs).G p
    have hu : unstack ((Zonotope.stackProd zs).c +
        ∑ p : Fin (∑ i, (zs i).h), β p • (Zonotope.stackProd zs).G p) = unstack z := by
      funext i
      rw [Zonotope.stackProd_value zs β i, hz i]
      simp only [hβi]
    calc z = stack (unstack z) := (stack_unstack z).symm
      _ = stack (unstack ((Zonotope.stackProd zs).c +
          ∑ p : Fin (∑ i, (zs i).h), β p • (Zonotope.stackProd zs).G p)) := by rw [hu]
      _ = _ := stack_unstack _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
