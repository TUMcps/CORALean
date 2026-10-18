module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic

@[expose] public section

/-!
# `SpectraShadow.supportFunc_eq_of_complementary`

Complementary slackness: a feasible `β` with `tr((A₀ + Σ βᵢ Aᵢ) Y) = 0` makes the dual bound the
supremum, attained at `c₀ + Σ βᵢ Gᵢ`. The exact value, not an enclosure.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFunc_eq_of_complementary (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (Y : Mat ℝ S.k S.k) (hY : Y.PosSemidef) (hc : ∀ i, (S.A i * Y).trace = - c (S.G i))
    (β : Fin S.m → ℝ) (hβ : (S.A₀ + ∑ i, β i • S.A i).PosSemidef)
    (hslack : ((S.A₀ + ∑ i, β i • S.A i) * Y).trace = 0) : -- --- STMT ---
    S.supportFunc c = ((c S.c + (S.A₀ * Y).trace : ℝ) : EReal)
      ∧ c (S.c + ∑ i, β i • S.G i) = c S.c + (S.A₀ * Y).trace := by -- --- PROOF ---
  -- the point's value, from the slack and the certificate
  have hval : c (S.c + ∑ i, β i • S.G i) = c S.c + (S.A₀ * Y).trace := by
    rw [SpectraShadow.trace_lmi_mul] at hslack
    have hs : ∑ i, β i * (S.A i * Y).trace = - ∑ i, β i * c (S.G i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring
    rw [hs] at hslack
    rw [map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    linarith
  -- weak duality is the upper bound, and the point reaches it
  refine ⟨le_antisymm (S.supportFunc_le_supportBound c Y hY hc) ?_, hval⟩
  rw [← hval]
  exact S.le_supportFunc_of_mem c ⟨β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
