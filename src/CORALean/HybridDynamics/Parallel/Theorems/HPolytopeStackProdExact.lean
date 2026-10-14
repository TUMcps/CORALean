module

public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdA
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdb
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdAe
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdbe
public import CORALean.HybridDynamics.Parallel.Theorems.Basic

@[expose] public section

/-!
# `HPolytope.stackProd` is the Cartesian product, exactly

A point of the stacked space is in the product of the halfspace descriptions exactly when each
of its blocks is in its component's. An equality, not an inclusion.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.stackProd_exact (gs : ∀ i, HPolytope (Vec ℝ (n i))) :
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
      rw [HPolytope.stackProd_Ae, HPolytope.stackProd_be] at h
      exact h
  · intro h
    refine ⟨fun r => ?_, fun r => ?_⟩
    · obtain ⟨⟨i, s⟩, rfl⟩ := finSigmaFinEquiv.surjective r
      rw [HPolytope.stackProd_A, HPolytope.stackProd_b]
      exact (h i).1 s
    · obtain ⟨⟨i, s⟩, rfl⟩ := finSigmaFinEquiv.surjective r
      rw [HPolytope.stackProd_Ae, HPolytope.stackProd_be]
      exact (h i).2 s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
