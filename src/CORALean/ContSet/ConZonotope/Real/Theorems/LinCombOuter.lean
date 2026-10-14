module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.AbsSmulCoeffLeOne
public import CORALean.ContSet.ConZonotope.Real.Theorems.SumUnivLinComb
public import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledComap

@[expose] public section

/-!
# `ConZonotope.linComb` encloses every segment between the two

The coefficients a point `λ y₁ + (1 - λ) y₂` needs are the two sets' own,
weighted: `λ β₁` and `(1 - λ) β₂`, with `2λ - 1` on the interpolation
generator. Every row of a scaled constraint is then its unscaled row times a
nonnegative weight, which is the whole argument.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linComb_outer (cZ₁ cZ₂ : ConZonotope α) :
    Set.linComb cZ₁.construct cZ₂.construct ⊆ (cZ₁.linComb cZ₂).construct := by -- --- PROOF ---
  rintro x ⟨y₁, ⟨β₁, hβ₁, hP₁, rfl⟩, y₂, ⟨β₂, hβ₂, hP₂, rfl⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  have hd₁ : β₁ ∈ cZ₁.domain.construct := ConZonotope.mem_domain_iff.mpr ⟨hβ₁, hP₁⟩
  have hd₂ : β₂ ∈ cZ₂.domain.construct := ConZonotope.mem_domain_iff.mpr ⟨hβ₂, hP₂⟩
  have hm0 : (0:ℝ) ≤ 1 - lam := by linarith
  have hm1 : (1:ℝ) - lam ≤ 1 := by linarith
  -- the concatenated coefficient vector: the two scaled blocks, then the weight
  set βc := Fin.append (Fin.append (lam • β₁) ((1 - lam) • β₂)) fun _ : Fin 1 => 2 * lam - 1
  -- stated at their own instances, since the goal spells the count as a projection
  have hpar : ((blockLast (cZ₁.h + cZ₂.h)) βc + 1) / 2 = lam := by
    rw [blockLast_append]
    ring
  have hpar' : (((-blockLast (cZ₁.h + cZ₂.h)) βc) + 1) / 2 = 1 - lam := by
    rw [LinearMap.neg_apply, blockLast_append]
    ring
  -- and each block is read off the concatenation by the map its constraints were pulled back along
  have hf₁ : ((blockLeft cZ₁.h cZ₂.h).comp (blockLeft (cZ₁.h + cZ₂.h) 1)) βc = lam • β₁ := by
    rw [LinearMap.comp_apply, blockLeft_append, blockLeft_append]
  have hf₂ : ((blockRight cZ₁.h cZ₂.h).comp (blockLeft (cZ₁.h + cZ₂.h) 1)) βc
      = (1 - lam) • β₂ := by
    rw [LinearMap.comp_apply, blockLeft_append, blockRight_append]
  refine ⟨βc, ?_, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa [βc] using ConZonotope.abs_smul_coeff_le_one hl0 hl1 hβ₁ j
      · intro j
        simpa [βc] using ConZonotope.abs_smul_coeff_le_one hm0 hm1 hβ₂ j
    · intro _
      simp only [βc, Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  -- each block answers to its own constraints at the weight the parameter names
  · exact HPolytope.mem_intersection_iff.mpr
      ⟨HPolytope.mem_halfScaled_comap hpar hl0 hd₁ hf₁,
        HPolytope.mem_halfScaled_comap hpar' hm0 hd₂ hf₂⟩
  -- the value: each block gives back its own weighted sum, the fresh generator the centres
  · have hs₁ : (∑ j, (lam * β₁ j) • cZ₁.G j) = lam • ∑ j, β₁ j • cZ₁.G j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul lam (β₁ j) (cZ₁.G j)
    have hs₂ : (∑ j, ((1 - lam) * β₂ j) • cZ₂.G j) = (1 - lam) • ∑ j, β₂ j • cZ₂.G j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul (1 - lam) (β₂ j) (cZ₂.G j)
    rw [ConZonotope.sum_univ_linComb, Fin.sum_univ_add]
    simp only [βc, ConZonotope.linComb, Fin.append_left, Fin.append_right, Fin.sum_univ_one,
      Pi.smul_apply, smul_eq_mul]
    rw [hs₁, hs₂]
    module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
