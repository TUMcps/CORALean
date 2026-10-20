module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The semidefinite relaxations are minima

The definitions Eq. 38 of [1, Thm. 17] and Eq. 41 of [1, Thm. 19] take a minimum of
`½ (‖v‖_{s₁} + ‖w‖_{s₂})` over the pairs `(v, w)` with
`[Diag(v), 0; 0, H Diag(w) Hᵀ] ≼ [0, Gᵀ; G, 0]`. For `H` onto the minimum exists. The set is
non-empty: with `R` a right inverse of `H` and `c = Σ (RG)²ᵢⱼ`, the pair `v = -c 1`, `w = -1`
works, since `2 zᵀ G α = 2 (Hᵀ z)ᵀ (R G α) ≥ -‖Hᵀ z‖² - c ‖α‖²` by Cauchy–Schwarz. The set is
closed, and the objective is a continuous function bounding every entry, so its sublevel set
at that pair is compact and the minimum is attained there.

## Inputs
* `s₁` – exponent of the first diagonal norm
* `s₂` – exponent of the second diagonal norm
* `G` – coupling matrix
* `H` – generator matrix of the second block

## Hypotheses
* `hH` – the generator matrix is onto

## Conclusion
* the relaxation's minimum over feasible pairs is attained

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The quadratic form of `[0, Gᵀ; G, 0] - [Diag(v), 0; 0, H Diag(w) Hᵀ]` at `(α, z)`. -/
theorem aux_srm_quad (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (v : Fin m → ℝ) (w : Fin l → ℝ) (x : Fin m ⊕ Fin n → ℝ) : -- --- CONCL ---
    x ⬝ᵥ ((fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)) *ᵥ x) =
      2 * ((x ∘ Sum.inr) ⬝ᵥ (G *ᵥ (x ∘ Sum.inl))) - ∑ j, v j * (x (Sum.inl j)) ^ 2 -
        ∑ i, w i * ((x ∘ Sum.inr) ᵥ* H) i ^ 2 := by -- --- PROOF ---
  rw [← Sum.elim_comp_inl_inr x]
  simp only [sub_mulVec, dotProduct_sub, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, sumElim_dotProduct_sumElim, zero_mulVec, zero_add, add_zero]
  have h1 : (x ∘ Sum.inl) ⬝ᵥ (Gᵀ *ᵥ (x ∘ Sum.inr)) = (x ∘ Sum.inr) ⬝ᵥ (G *ᵥ (x ∘ Sum.inl)) := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  have h3 : (x ∘ Sum.inl) ⬝ᵥ (diagonal v *ᵥ (x ∘ Sum.inl)) =
      ∑ j, v j * (x (Sum.inl j)) ^ 2 := by
    simp only [mulVec_diagonal, dotProduct, Function.comp_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : (x ∘ Sum.inr) ⬝ᵥ ((H * diagonal w * Hᵀ) *ᵥ (x ∘ Sum.inr)) =
      ∑ i, w i * ((x ∘ Sum.inr) ᵥ* H) i ^ 2 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Sum.elim_comp_inl_inr]
  rw [h1, h3, h4]
  ring

/-- `|vⱼ|` is at most `‖v‖_s`. -/
theorem aux_srm_abs_le (s : ℝ≥0∞) [Fact (1 ≤ s)] {k : ℕ} (v : Fin k → ℝ) (j : Fin k) :
    |v j| ≤ ‖WithLp.toLp s v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp s v) j


-- =======================================  MAIN THEOREM  ======================================= --

theorem sdp_relaxation_exists_isLeast (s₁ s₂ : ℝ≥0∞) [Fact (1 ≤ s₁)] [Fact (1 ≤ s₂)]
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) : -- --- CONCL ---
    ∃ Z, IsLeast ((fun vw : (Fin m → ℝ) × (Fin l → ℝ) =>
        (‖WithLp.toLp s₁ vw.1‖ + ‖WithLp.toLp s₂ vw.2‖) / 2) ''
        {vw | (fromBlocks 0 Gᵀ G 0 -
          fromBlocks (diagonal vw.1) 0 0 (H * diagonal vw.2 * Hᵀ)).PosSemidef})
        Z := by -- --- PROOF ---
  set K : Set ((Fin m → ℝ) × (Fin l → ℝ)) := {vw | (fromBlocks 0 Gᵀ G 0 -
    fromBlocks (diagonal vw.1) 0 0 (H * diagonal vw.2 * Hᵀ)).PosSemidef} with hKdef
  set obj : (Fin m → ℝ) × (Fin l → ℝ) → ℝ :=
    fun vw => (‖WithLp.toLp s₁ vw.1‖ + ‖WithLp.toLp s₂ vw.2‖) / 2 with hobj
  -- the symmetric matrices of `K`
  have hherm : ∀ vw : (Fin m → ℝ) × (Fin l → ℝ), (fromBlocks 0 Gᵀ G 0 -
      fromBlocks (diagonal vw.1) 0 0 (H * diagonal vw.2 * Hᵀ)).IsHermitian := fun vw => by
    ext a b
    rcases a with j | k <;> rcases b with j' | k' <;>
      simp [diagonal_apply, eq_comm, mul_apply, mul_comm, mul_left_comm]
    split_ifs with h <;> simp [h]
  have hKeq : K = ⋂ x : Fin m ⊕ Fin n → ℝ, {vw | 0 ≤ 2 * ((x ∘ Sum.inr) ⬝ᵥ (G *ᵥ (x ∘ Sum.inl))) -
      ∑ j, vw.1 j * (x (Sum.inl j)) ^ 2 - ∑ i, vw.2 i * ((x ∘ Sum.inr) ᵥ* H) i ^ 2} := by
    ext vw
    simp only [hKdef, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h x
      rw [← aux_srm_quad]
      simpa using h.dotProduct_mulVec_nonneg x
    · intro h
      refine PosSemidef.of_dotProduct_mulVec_nonneg (hherm vw) fun x => ?_
      simpa [aux_srm_quad] using h x
  have hKc : IsClosed K := by
    rw [hKeq]
    exact isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)
  -- a point of `K`: `v = -c 1`, `w = -1`
  choose β hβ using fun k : Fin n => hH (Pi.single k 1)
  set Y : Matrix (Fin l) (Fin m) ℝ := (Matrix.of fun i k => β k i) * G with hYdef
  have hHY : H * Y = G := by
    have : H * Matrix.of (fun i k => β k i) = 1 := by
      ext k k'
      have := congrFun (hβ k') k
      simpa [mul_apply, mulVec, dotProduct, Pi.single_apply, one_apply, eq_comm] using this
    rw [hYdef, ← Matrix.mul_assoc, this, Matrix.one_mul]
  set c : ℝ := ∑ i, ∑ j, Y i j ^ 2
  set vw₀ : (Fin m → ℝ) × (Fin l → ℝ) := (fun _ => -c, fun _ => -1)
  have hvw₀ : vw₀ ∈ K := by
    rw [hKeq]
    simp only [Set.mem_iInter, Set.mem_setOf_eq, vw₀]
    intro x
    set α := x ∘ Sum.inl
    set u := (x ∘ Sum.inr) ᵥ* H
    -- `zᵀ G α = uᵀ (Y α)`, and `2 uᵢ (Yα)ᵢ ≥ -uᵢ² - (Yα)ᵢ²`, `Σ (Yα)ᵢ² ≤ c ‖α‖²`
    have hzG : (x ∘ Sum.inr) ⬝ᵥ (G *ᵥ α) = u ⬝ᵥ (Y *ᵥ α) := by
      rw [← hHY, ← mulVec_mulVec, dotProduct_mulVec]
    have hCS : ∀ i, (Y *ᵥ α) i ^ 2 ≤ (∑ j, Y i j ^ 2) * ∑ j, α j ^ 2 := fun i => by
      simpa [mulVec, dotProduct] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (Y i) α
    have h2 : ∀ i, -(u i ^ 2) - (Y *ᵥ α) i ^ 2 ≤ 2 * (u i * (Y *ᵥ α) i) := fun i => by
      nlinarith [sq_nonneg (u i + (Y *ᵥ α) i)]
    have hsum : ∑ i, (Y *ᵥ α) i ^ 2 ≤ c * ∑ j, α j ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hCS i
    have hdot : -(∑ i, u i ^ 2) - ∑ i, (Y *ᵥ α) i ^ 2 ≤ 2 * (u ⬝ᵥ (Y *ᵥ α)) := by
      rw [dotProduct, Finset.mul_sum, neg_sub_left, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun i _ => by linarith [h2 i]
    rw [hzG]
    simp only [neg_mul, one_mul, Finset.sum_neg_distrib, sub_neg_eq_add, ← Finset.mul_sum]
    have : ∑ j, x (Sum.inl j) ^ 2 = ∑ j, α j ^ 2 := rfl
    rw [this]
    linarith
  -- the sublevel set at `vw₀` is compact
  set S := K ∩ {vw | obj vw ≤ obj vw₀}
  have hobjc : Continuous obj := by
    simp only [hobj]
    exact ((continuous_norm.comp ((PiLp.continuous_toLp s₁ _).comp continuous_fst)).add
      (continuous_norm.comp ((PiLp.continuous_toLp s₂ _).comp continuous_snd))).div_const 2
  -- the objective bounds every entry
  have hSb : S ⊆ Metric.closedBall 0 (2 * obj vw₀) := fun vw ⟨_, hvw⟩ => by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := norm_nonneg (WithLp.toLp s₁ vw.1)
    have h2 := norm_nonneg (WithLp.toLp s₂ vw.2)
    simp only [Set.mem_setOf_eq, hobj] at hvw
    refine max_le ((pi_norm_le_iff_of_nonneg (by simp only [hobj] at *; linarith)).mpr
      fun j => ?_) ((pi_norm_le_iff_of_nonneg (by simp only [hobj] at *; linarith)).mpr
      fun i => ?_)
    · rw [Real.norm_eq_abs]
      have := aux_srm_abs_le s₁ vw.1 j
      simp only [hobj]; linarith
    · rw [Real.norm_eq_abs]
      have := aux_srm_abs_le s₂ vw.2 i
      simp only [hobj]; linarith
  have hSc : IsCompact S :=
    (isCompact_closedBall _ _).of_isClosed_subset (hKc.inter (isClosed_le hobjc continuous_const))
      hSb
  -- a minimizer on the sublevel set wins over all of `K`
  obtain ⟨vw, ⟨hvwK, -⟩, hmin⟩ := hSc.exists_isMinOn
    ⟨vw₀, hvw₀, show obj vw₀ ≤ obj vw₀ from le_rfl⟩ hobjc.continuousOn
  refine ⟨obj vw, ⟨vw, hvwK, rfl⟩, ?_⟩
  rintro _ ⟨vw', hvw', rfl⟩
  by_cases h : obj vw' ≤ obj vw₀
  · exact hmin ⟨hvw', h⟩
  · exact (hmin ⟨hvw₀, show obj vw₀ ≤ obj vw₀ from le_rfl⟩).trans (le_of_not_ge h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
