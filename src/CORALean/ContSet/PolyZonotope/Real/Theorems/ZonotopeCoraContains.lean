import CORALean.ContSet.PolyZonotope.Real.Operations.ZonotopeCora
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope

/-!
# `zonotopeCora` encloses the polynomial zonotope

A column of even exponents has its monomial in `[0,1]`, so `2m - 1` is an admissible
coefficient on the half that stays free, and the centre's half plus this makes `m`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficient the free half of generator `i` is given. -/
noncomputable def PolyZonotope.aux_coraCoeff {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin p → ℝ) (i : Fin h) : ℝ :=
  if ∀ k, E k i % 2 = 0 then 2 * PolyZonotope.monomial E a i - 1
  else PolyZonotope.monomial E a i

theorem PolyZonotope.aux_coraWeight_smul {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    (1 - PolyZonotope.coraWeight E i)
        + PolyZonotope.aux_coraCoeff E a i * PolyZonotope.coraWeight E i
      = PolyZonotope.monomial E a i := by
  rw [PolyZonotope.coraWeight, PolyZonotope.aux_coraCoeff]
  split_ifs <;> ring

/-- An all-even column's monomial never goes below zero. -/
theorem PolyZonotope.aux_coraMonomial_nonneg {p h : ℕ} {E : Fin p → Fin h → ℕ} {i : Fin h}
    (hE : ∀ k, E k i % 2 = 0) (a : Fin p → ℝ) : 0 ≤ PolyZonotope.monomial E a i :=
  Finset.prod_nonneg fun k _ => Even.pow_nonneg (Nat.even_iff.mpr (hE k)) (a k)

theorem PolyZonotope.aux_abs_coraCoeff_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) :
    |PolyZonotope.aux_coraCoeff E a i| ≤ 1 := by -- --- PROOF ---
  rw [PolyZonotope.aux_coraCoeff]
  split_ifs with he
  · have h₀ : 0 ≤ PolyZonotope.monomial E a i := PolyZonotope.aux_coraMonomial_nonneg he a
    have h₁ : PolyZonotope.monomial E a i ≤ 1 :=
      le_trans (le_abs_self _) (PolyZonotope.abs_monomial_le_one E ha i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact PolyZonotope.abs_monomial_le_one E ha i


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotopeCora_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonotopeCora.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (fun i => PolyZonotope.aux_coraCoeff pZ.E a i) b, ?_, ?_⟩
  -- every coefficient is admissible: the free half's, and the independent block's unchanged
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.aux_abs_coraCoeff_le_one pZ.E ha i
    · intro j
      simpa using hb j
  -- the centre's share plus the free half's coefficient times its weight is the monomial
  · have hsum : ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        = ∑ i, (1 - PolyZonotope.coraWeight pZ.E i) • pZ.G i
          + ∑ i, PolyZonotope.aux_coraCoeff pZ.E a i
              • (PolyZonotope.coraWeight pZ.E i • pZ.G i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, PolyZonotope.aux_coraWeight_smul]
    have hs : ∀ f : Fin (pZ.h + pZ.q) → α, ∑ l : Fin (pZ.h + pZ.q), f l
        = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) := fun f => Fin.sum_univ_add f
    -- the sum over all generators is the dependent part plus the independent one
    show _ = pZ.c + ∑ i, (1 - PolyZonotope.coraWeight pZ.E i) • pZ.G i
      + ∑ l : Fin (pZ.h + pZ.q), Fin.append (fun i => PolyZonotope.aux_coraCoeff pZ.E a i) b l
        • Fin.append (fun i => PolyZonotope.coraWeight pZ.E i • pZ.G i) pZ.GI l
    rw [hs]
    simp only [Fin.append_left, Fin.append_right]
    rw [hsum]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
