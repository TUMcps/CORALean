module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ConZonotope

@[expose] public section

/-!
# A hull as a constrained zonotope: `mem_simplex_iff`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mem_simplex_iff {k : ℕ} {β : Vec ℝ k} :
    β ∈ (VPolytope.simplex k).construct ↔ (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 := by -- --- PROOF ---
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h : -(β j) ≤ 0 := hle j
      linarith
    · -- restated at `Fin 1`, the row count's reduced spelling, so the index elaborates
      have heq' : ∀ _ : Fin 1, (∑ j, LinearMap.proj j : Vec ℝ k →ₗ[ℝ] ℝ) β = 1 := heq
      have h := heq' 0
      rwa [LinearMap.sum_apply] at h
  · rintro ⟨hnn, hsum⟩
    refine ⟨fun j => ?_, fun _ => ?_⟩
    · show -(β j) ≤ 0
      linarith [hnn j]
    · show (∑ j, LinearMap.proj j : Vec ℝ k →ₗ[ℝ] ℝ) β = 1
      rwa [LinearMap.sum_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
