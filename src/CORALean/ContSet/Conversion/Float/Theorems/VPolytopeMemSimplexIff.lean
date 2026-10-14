module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.NegIdentityMatMulVec
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConZonotope

@[expose] public section

/-!
# A hull as a constrained zonotope, over a floating-point scalar: `mem_simplex_iff`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem VPolytope.aux_ones_mulVec (β : Vec ℝ k) (i : Fin 1) :
    (toRealMat (fun (_ : Fin 1) (_ : Fin k) => (one : 𝕋)) *ᵥ β) i = ∑ j, β j := by
  show ∑ j, toReal (one : 𝕋) * β j = ∑ j, β j
  exact Finset.sum_congr rfl fun j _ => by rw [toReal_one, one_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mem_simplex_iff {β : Vec ℝ k} :
    β ∈ (VPolytope.simplex 𝕋 k).construct ↔ (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 := by -- --- PROOF ---
  simp only [VPolytope.simplex]
  rw [HPolytope.mem_intersection_iff, HPolytope.mem_ineqs_iff, HPolytope.mem_eqs_iff]
  -- both directions: a nonnegativity row each, and the two ends of the ones-row equality
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h := hle j
      rw [negIdentityMat_mulVec, toReal_zero] at h
      linarith
    · have h := heq 0
      rw [VPolytope.aux_ones_mulVec] at h
      have h₁ : toReal (one : 𝕋) ≤ ∑ j, β j := h.1
      have h₂ : ∑ j, β j ≤ toReal (one : 𝕋) := h.2
      rw [toReal_one] at h₁ h₂
      linarith
  · rintro ⟨hnn, hsum⟩
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [negIdentityMat_mulVec, toReal_zero]
      linarith [hnn j]
    · rw [VPolytope.aux_ones_mulVec, hsum, toReal_one]
      exact ⟨le_refl 1, le_refl 1⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
