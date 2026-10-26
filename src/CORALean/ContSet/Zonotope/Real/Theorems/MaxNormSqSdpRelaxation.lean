module

public import CORALean.ContSet.Zonotope.Real.Theorems.MaxNormSqEqSign
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import CORALean.Global.DiagSdpStrongDuality

@[expose] public section

/-!
# The maximum zonotope norm as a rank-one semidefinite program, and its relaxation

[1, Eq. 19]: `p* = max ⟨GᵀG, U⟩` s.t. `U ≽ 0`, `⟨diag(eᵢ), U⟩ = 1`, `rank(U) = 1`, where
`U = u uᵀ`; dropping the rank constraint gives a relaxation whose dual is (18), and strong duality
holds between the two. With the rank constraint, `Uᵢᵢ = uᵢ² = 1` makes `u` a sign vector and
`⟨GᵀG, u uᵀ⟩ = ‖G u‖₂²`, so the program is (17), whose optimum `⌈Z⌉²` is attained at a sign vector
(`Zonotope.maxNormSq_eq_sign`). The relaxation and (18) attain the same optimum by
`diag_sdp_strong_duality`; the dual's `λ ≥ 0` is free, the diagonal of `diag(λ) - GᵀG ≽ 0` being
non-negative. So the gap of `Lemma 3` is the rank constraint's alone.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the semidefinite relaxation has equal optimal and dual values

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". 2020 American Control Conference (ACC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `⟨M, u uᵀ⟩ = uᵀ M u`. -/
private theorem aux_maxNormSqSdp_trace_vecMulVec {m : ℕ} (M : Mat ℝ m m) (u : Vec ℝ m) :
    (M * vecMulVec u u).trace = u ⬝ᵥ (M *ᵥ u) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.maxNormSq_sdp_relaxation (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    IsGreatest {t | ∃ U : Mat ℝ Z.h Z.h, U.PosSemidef ∧ (∀ j, U j j = 1) ∧
        (∃ u : Vec ℝ Z.h, U = vecMulVec u u) ∧
        t = ((Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) * U).trace} Z.maxNormSq ∧
      ∃ d : ℝ,
        IsGreatest {t | ∃ U : Mat ℝ Z.h Z.h, U.PosSemidef ∧ (∀ j, U j j = 1) ∧
          t = ((Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) * U).trace} d ∧
        IsLeast {t | ∃ lam : Fin Z.h → ℝ, (∀ j, 0 ≤ lam j) ∧
          (diagonal lam - Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k).PosSemidef ∧
          t = ∑ j, lam j} d := by -- --- PROOF ---
  set Gram : Mat ℝ Z.h Z.h := Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k with hGram
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the sign vector at which `⌈Z⌉²` is attained
    set σ : (Fin Z.h → Bool) → Vec ℝ Z.h := fun s j => if s j then (1 : ℝ) else -1 with hσ
    obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      fun s => σ s ⬝ᵥ (((0 : ℝ) • (1 : Mat ℝ Z.h Z.h) - Gram) *ᵥ σ s)
    have hval := (Z.maxNormSq_eq_sign 0).1
    rw [hs₀] at hval
    refine ⟨vecMulVec (σ s₀) (σ s₀), ?_, fun j => ?_, ⟨σ s₀, rfl⟩, ?_⟩
    · simpa using posSemidef_vecMulVec_self_star (σ s₀)
    · simp only [vecMulVec_apply, hσ]; split_ifs <;> norm_num
    · rw [aux_maxNormSqSdp_trace_vecMulVec, hval, zero_smul, zero_sub, Matrix.neg_mulVec,
        dotProduct_neg, neg_neg, zero_mul, add_zero]
  · -- `Uᵢᵢ = uᵢ² = 1`, so `⟨GᵀG, u uᵀ⟩ = ‖G u‖₂² ≤ ⌈Z⌉²`
    rintro _ ⟨_, -, hd, ⟨u, rfl⟩, rfl⟩
    have hu : ∀ j, |u j| ≤ 1 := fun j => by
      have h := hd j
      simp only [vecMulVec_apply] at h
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u j - 1), sq_nonneg (u j + 1)]
    rw [aux_maxNormSqSdp_trace_vecMulVec, hGram, ← Z.sq_norm₂_sum_eq_gram]
    exact Z.sq_norm₂_le_maxNormSq hu
  · -- the relaxation and (18): strong duality, `λ ≥ 0` being implied
    have hsymm : Gramᵀ = Gram := by
      ext j k; simp [hGram, dotProduct_comm]
    obtain ⟨d, hP, hD⟩ := diag_sdp_strong_duality Gram hsymm
    refine ⟨d, hP, ⟨?_, ?_⟩⟩
    · obtain ⟨lam, hlam, hd⟩ := hD.1
      refine ⟨lam, fun j => ?_, hlam, hd⟩
      have h1 := hlam.diag_nonneg (i := j)
      have h2 : 0 ≤ Gram j j := by
        simp only [hGram, of_apply, dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      simp only [Matrix.sub_apply, diagonal_apply_eq] at h1
      linarith
    · rintro _ ⟨lam, -, hlam, rfl⟩
      exact hD.2 ⟨lam, hlam, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
