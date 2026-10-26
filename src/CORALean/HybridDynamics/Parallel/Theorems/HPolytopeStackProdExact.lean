module

public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdA
public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdAe
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdb

@[expose] public section

/-!
# `HPolytope.stackProd` is the Cartesian product, exactly

A point of the stacked space is in the product of the halfspace descriptions exactly when each
of its blocks is in its component's. An equality, not an inclusion.

## Inputs
* `gs` – halfspace descriptions of the components

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `HPolytope.stackProd`'s rows at a pair. -/
private theorem HPolytope.aux_stackProd_be (gs : ∀ i, HPolytope (Vec ℝ (n i))) (i : Fin k)
    (s : Fin (gs i).me) :
    (HPolytope.stackProd gs).be (finSigmaFinEquiv ⟨i, s⟩) =
      (gs i).be s :=
  congrArg (fun p : (Σ i, Fin (gs i).me) => (gs p.1).be p.2) (Equiv.symm_apply_apply _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.stackProd_exact (gs : ∀ i, HPolytope (Vec ℝ (n i))) : -- --- CONCL ---
    (HPolytope.stackProd gs).construct =
      {z | ∀ i, unstack z i ∈ (gs i).construct} := by -- --- PROOF ---
  ext z
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨fun s => ?_, fun s => ?_⟩
    · have h := h1 (finSigmaFinEquiv ⟨i, s⟩)
      rw [HPolytope.stackProd_A, HPolytope.stackProd_b] at h
      exact h
    · have h := h2 (finSigmaFinEquiv ⟨i, s⟩)
      rw [HPolytope.stackProd_Ae, HPolytope.aux_stackProd_be] at h
      exact h
  · intro h
    refine ⟨fun r => ?_, fun r => ?_⟩
    · obtain ⟨⟨i, s⟩, rfl⟩ := finSigmaFinEquiv.surjective r
      rw [HPolytope.stackProd_A, HPolytope.stackProd_b]
      exact (h i).1 s
    · obtain ⟨⟨i, s⟩, rfl⟩ := finSigmaFinEquiv.surjective r
      rw [HPolytope.stackProd_Ae, HPolytope.aux_stackProd_be]
      exact (h i).2 s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
