module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.NegIdentityMatMulVec
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsConstructIff

@[expose] public section

/-!
# A hull as a constrained zonotope, over a floating-point scalar: `mem_simplex_iff`

## Inputs
* `β` – coefficient vector

## Hypotheses
* none

## Conclusion
* membership in simplex means nonnegative and sum one
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

theorem VPolytope.mem_simplex_iff {β : Vec ℝ k} : -- --- CONCL ---
    β ∈ (VPolytope.simplex 𝕋 k).construct ↔ (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 := by -- --- PROOF ---
  simp only [VPolytope.simplex]
  rw [HPolytope.mem_stackRows_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)
    (HPolytope.errFree_of_origin rfl rfl rfl), HPolytope.mem_ineqs_iff, HPolytope.mem_eqs_iff]
  -- both directions: a nonnegativity row each, and the ones-row equality
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h := hle j
      rw [negIdentityMat_mulVec, toReal_zero] at h
      linarith
    · have h := heq 0
      rw [VPolytope.aux_ones_mulVec, toReal_one] at h
      exact h
  · rintro ⟨hnn, hsum⟩
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [negIdentityMat_mulVec, toReal_zero]
      linarith [hnn j]
    · rw [VPolytope.aux_ones_mulVec, hsum, toReal_one]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
