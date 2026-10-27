module

public import CORALean.Global.CoeffNormLeDual
public import CORALean.Global.DiagBlockSdpDual
public import CORALean.Global.DotProductLeCoeffNorm
public import CORALean.Global.GaussianNormMomentLe
public import CORALean.Global.GaussianSignCorrelation
public import CORALean.Global.PosSemidefGram
public import CORALean.Global.SdpRelaxationQuadLe

@[expose] public section

/-!
# The semidefinite relaxation of zonotope-in-ellipsotope containment

[1, Thm. 17]: for `H` onto and `q ∈ (1, 2]`, `ZSR_q = ½ min_K (‖v‖₁ + ‖w‖_{q/(2-q)})` (Eq. 38), `K`
the `(v, w)` with `[Diag(v), 0; 0, H Diag(w) Hᵀ] ≼ [0, Gᵀ; G, 0]` (Eq. 39), has
`r ≤ ZSR_q ≤ (γ_{q*}/γ₁) r` (Eq. 40), `r` the greatest `coeffNorm H` over the cube and `γ_k` the
constant of Eq. 31; the minimum exists (`sdp_relaxation_exists_isLeast`). The paper cites Thm. 5.6
of its reference 22; here the proof is written out: `r ≤ ZSR_q` by `exists_dual_coeffNorm_le` and
`sdp_relaxation_quad_le`; for the upper bound a certificate `X ≽ 0` (`diag_block_sdp_exists_dual`)
is rounded at a standard Gaussian, and `integral_inner_mul_sign_inner_stdGaussian` and
`gaussian_norm_moment_le` bound the two sides' expectations.

## Inputs
* `q` – exponent of the coefficient norm
* `q'` – its conjugate exponent
* `G` – zonotope generator matrix
* `H` – ellipsotope generator matrix
* `ZSR` – relaxation value
* `r` – containment radius

## Hypotheses
* `hq1` – the exponent exceeds one
* `hq2` – the exponent is at most two
* `hH` – the ellipsotope generator matrix is onto
* `hZSR` – the relaxation value is the least feasible one
* `hr` – the radius is the greatest norm over the cube

## Conclusion
* the radius is at most the relaxation value, which is at most a Gaussian constant times the radius

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal NNReal RealInnerProductSpace
open Matrix MeasureTheory ProbabilityTheory

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_zsr_two_sub_one : (2 : ℝ≥0∞) - 1 = 1 := by
  rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm,
    ENNReal.add_sub_cancel_right ENNReal.one_ne_top]

/-- `q / (2 - q)` and `q* / 2` are Hölder conjugates for `q ∈ (1, 2]`. -/
private theorem aux_zsr_holderConjugate {q q' : ℝ≥0∞} [q.HolderConjugate q'] (hq1 : 1 < q)
    (hq2 : q ≤ 2) : -- --- CONCL ---
    (q / (2 - q)).HolderConjugate (q' / 2) := by -- --- PROOF ---
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hqT : q ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hq2
  rw [ENNReal.holderConjugate_iff, ENNReal.inv_div (Or.inl (by simp)) (Or.inr hq0),
    ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp)), ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, mul_comm, ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr hq0),
    ENNReal.mul_inv_cancel hq0 hqT, ← ENNReal.HolderConjugate.one_sub_inv q q',
    ENNReal.sub_mul (fun _ _ => by simp), one_mul, mul_comm q⁻¹ 2]
  -- `(2q⁻¹ - 1) + (2 - 2q⁻¹) = 1`, as `1 ≤ 2q⁻¹ ≤ 2`
  have h1 : 1 ≤ 2 * q⁻¹ := by
    rw [mul_comm, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hqT),
      one_mul]
    exact hq2
  have h2 : 2 * q⁻¹ ≤ 2 := by
    calc 2 * q⁻¹ ≤ 2 * 1 := by
          gcongr
          exact ENNReal.inv_le_one.mpr hq1.le
      _ = 2 := mul_one 2
  rw [add_comm, tsub_add_tsub_cancel h2 h1]
  exact aux_zsr_two_sub_one

private theorem aux_zsr_one_le {q : ℝ≥0∞} (hq1 : 1 < q) (hq2 : q ≤ 2) : -- --- CONCL ---
    1 ≤ q / (2 - q) := by -- --- PROOF ---
  rcases eq_or_lt_of_le hq2 with rfl | hlt
  · rw [tsub_self, ENNReal.div_zero two_ne_zero]
    exact le_top
  · have hpos : 2 - q ≠ 0 := (tsub_pos_of_lt hlt).ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by simp)), one_mul]
    -- `2 - q ≤ 1 ≤ q`
    calc 2 - q ≤ 2 - 1 := tsub_le_tsub_left hq1.le 2
      _ = 1 := aux_zsr_two_sub_one
      _ ≤ q := hq1.le

/-- `‖(tᵢ²)ᵢ‖_{x/2} = ‖t‖_x²` for `2 ≤ x < ∞`. -/
private theorem aux_zsr_norm_sq {k : ℕ} {x : ℝ≥0∞} (hx : 2 ≤ x) (hxT : x ≠ ∞)
    (t : Fin k → ℝ) : -- --- CONCL ---
    ‖WithLp.toLp (x / 2) (fun i => t i ^ 2)‖ = ‖WithLp.toLp x t‖ ^ 2 := by -- --- PROOF ---
  have hc : 2 ≤ x.toReal := by
    have := ENNReal.toReal_mono hxT hx
    simpa using this
  have hx2 : (x / 2).toReal = x.toReal / 2 := by
    rw [ENNReal.toReal_div]; simp
  have h0 : 0 < x.toReal := by linarith
  rw [PiLp.norm_eq_sum (by rw [hx2]; linarith), PiLp.norm_eq_sum h0, hx2]
  -- termwise `|tᵢ²|^{x/2} = |tᵢ|^x`, then the outer root
  have hterm : ∀ i, ‖t i ^ 2‖ ^ (x.toReal / 2) = ‖t i‖ ^ x.toReal := fun i => by
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  simp only [hterm]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
  congr 1
  push_cast
  field_simp

private theorem aux_zsr_gaussMomentRoot_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ gaussMomentRoot p := by
  unfold gaussMomentRoot
  exact Real.rpow_nonneg (mul_nonneg (by positivity)
    (Real.Gamma_pos_of_pos (by linarith)).le) _

private theorem aux_zsr_gaussMomentRoot_pos : 0 < gaussMomentRoot 1 := by
  unfold gaussMomentRoot
  norm_num
  positivity

/-- `q* ≥ 2` for `q ≤ 2`. -/
private theorem aux_zsr_two_le_conj {q q' : ℝ≥0∞} [q.HolderConjugate q'] (hq2 : q ≤ 2) : 2 ≤ q' :=
    by
  rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv q q', ← ENNReal.one_sub_inv_two]
  exact tsub_le_tsub_left (ENNReal.inv_le_inv.mpr hq2) 1

/-- The weak half: a pair of `K` bounds the norm of every point of `Z(G)`. -/
private theorem aux_zsr_weak (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q'] (hq1 : 1 < q)
    (hq2 : q ≤ 2) (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) (v : Fin m → ℝ) (w : Fin l → ℝ)
    (hK : (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)).PosSemidef)
    {α : Fin m → ℝ} (hα : α ∈ Metric.closedBall (0 : Fin m → ℝ) 1) : -- --- CONCL ---
    coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
      (G *ᵥ α) ≤ (‖WithLp.toLp 1 v‖ + ‖WithLp.toLp (q / (2 - q)) w‖) / 2 := by -- --- PROOF ---
  haveI : (q / (2 - q)).HolderConjugate (q' / 2) := aux_zsr_holderConjugate hq1 hq2
  haveI : Fact (1 ≤ q / (2 - q)) := ⟨aux_zsr_one_le hq1 hq2⟩
  haveI : Fact (1 ≤ q' / 2) := ⟨ENNReal.HolderConjugate.one_le (q' / 2) (q / (2 - q))⟩
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  obtain ⟨z, hz, hle⟩ := exists_dual_coeffNorm_le q q' H (hH (G *ᵥ α))
  have hq := sdp_relaxation_quad_le 1 ∞ (q / (2 - q)) (q' / 2) G H v w hK α z
  -- `‖α²‖_∞ ≤ 1` and `‖(Hᵀ z)²‖_{q*/2} = ‖Hᵀ z‖_{q*}² ≤ 1`
  have hα2 : ‖WithLp.toLp ∞ (fun j => α j ^ 2)‖ ≤ 1 := by
    rw [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    have := (norm_le_pi_norm α j).trans (mem_closedBall_zero_iff.mp hα)
    rw [Real.norm_eq_abs] at this ⊢
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (α j), sq_abs (α j)]
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  have hz2 : ‖WithLp.toLp (q' / 2) (fun i => (z ᵥ* H) i ^ 2)‖ ≤ 1 := by
    rw [aux_zsr_norm_sq (aux_zsr_two_le_conj hq2) hqT]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hv0 := norm_nonneg (WithLp.toLp 1 v)
  have hw0 := norm_nonneg (WithLp.toLp (q / (2 - q)) w)
  have h1 := mul_le_mul_of_nonneg_left hα2 hv0
  have h2 := mul_le_mul_of_nonneg_left hz2 hw0
  linarith

/-- The vectors of a Gram factorization: `‖yⱼ‖`, `‖bᵢ‖²` and `⟨yⱼ, cⱼ⟩` in terms of `X`. -/
private theorem aux_zsr_gram {d : ℕ} (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
    (c : Fin m ⊕ Fin n → EuclideanSpace ℝ (Fin d))
    (hc : ∀ p q, X p q = ⟪c p, c q⟫) : -- --- CONCL ---
    (∀ i, ‖∑ k, H k i • c (Sum.inr k)‖ ^ 2 = (Hᵀ * X.toBlocks₂₂ * H) i i) ∧
      ∑ j, ⟪∑ k, G k j • c (Sum.inr k), c (Sum.inl j)⟫ =
        ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) := by -- --- PROOF ---
  refine ⟨fun i => ?_, ?_⟩
  · rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, ← hc, mul_apply,
      transpose_apply, toBlocks₂₂, of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  · simp only [sum_inner, real_inner_smul_left, ← hc]
    exact Finset.sum_comm

/-- The pointwise bound of the rounding: `Σⱼ sⱼ ⟨yⱼ, g⟩ sign⟨cⱼ, g⟩ ≤ r ‖(⟨bᵢ, g⟩)ᵢ‖_{q*}`. -/
private theorem aux_zsr_pointwise {d : ℕ} (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (hq' : q' ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {r : ℝ}
    (hrle : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm ((Matrix.mulVecLin H) ∘ₗ
      (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α) ≤ r)
    (c : Fin m ⊕ Fin n → EuclideanSpace ℝ (Fin d)) (s : Fin m → ℝ) (hs : ∀ j, |s j| ≤ 1)
    (g : EuclideanSpace ℝ (Fin d)) : -- --- CONCL ---
    ∑ j, s j * (⟪∑ k, G k j • c (Sum.inr k), g⟫ * (SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ)) ≤
      r * (∑ i, |⟪∑ k, H k i • c (Sum.inr k), g⟫| ^ q'.toReal) ^
        (1 / q'.toReal) := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  have hp0 : 0 < q'.toReal :=
    ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'
  set ζ : Fin n → ℝ := fun k => ⟪c (Sum.inr k), g⟫
  set α : Fin m → ℝ := fun j => s j * (SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ)
  have hα : α ∈ Metric.closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hsg : |(SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ)| ≤ 1 := by
      rcases lt_trichotomy ⟪c (Sum.inl j), g⟫ 0 with h | h | h <;> simp [h]
    nlinarith [hs j, abs_nonneg (s j), abs_nonneg ((SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ))]
  -- the rounded form is `ζᵀ G α` and the right side `‖Hᵀ ζ‖_{q*}`
  have hL : ∑ j, s j * (⟪∑ k, G k j • c (Sum.inr k), g⟫ *
      (SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ)) = ζ ⬝ᵥ (G *ᵥ α) := by
    rw [dotProduct_mulVec]
    simp only [dotProduct, vecMul, sum_inner, real_inner_smul_left, ζ, α]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Finset.sum_congr rfl fun k _ => mul_comm ⟪c (Sum.inr k), g⟫ (G k j)]
      ring
  have hR : ‖WithLp.toLp q' (ζ ᵥ* H)‖ =
      (∑ i, |⟪∑ k, H k i • c (Sum.inr k), g⟫| ^ q'.toReal) ^ (1 / q'.toReal) := by
    rw [PiLp.norm_eq_sum (by simpa using hp0)]
    simp only [vecMul, dotProduct, sum_inner, real_inner_smul_left, Real.norm_eq_abs, ζ]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      congr 2; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hL, ← hR]
  calc ζ ⬝ᵥ (G *ᵥ α) ≤ _ := dotProduct_le_coeffNorm_mul_norm q q' H (hH _) ζ
    _ ≤ r * ‖WithLp.toLp q' (ζ ᵥ* H)‖ := mul_le_mul_of_nonneg_right (hrle α hα) (norm_nonneg _)

/-- The rounding: a certificate `X` gives `γ₁ Σ G_{kj} X_{kj} ≤ γ_{q*} r`. -/
private theorem aux_zsr_rounding (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q'] (hq1 : 1 < q)
    (hq2 : q ≤ 2) (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {r : ℝ} (hr0 : 0 ≤ r)
    (hrle : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm ((Matrix.mulVecLin H) ∘ₗ
      (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α) ≤ r)
    (X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (hX : X.PosSemidef)
    (hX1 : ‖WithLp.toLp ∞ (fun j => X (Sum.inl j) (Sum.inl j))‖ ≤ 1)
    (hX2 : ‖WithLp.toLp (q' / 2) (fun i => (Hᵀ * X.toBlocks₂₂ * H) i i)‖ ≤ 1) : -- --- CONCL ---
    gaussMomentRoot 1 * ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) ≤
      r * gaussMomentRoot q'.toReal := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  have hq'2 := aux_zsr_two_le_conj (q' := q') hq2
  set p := q'.toReal with hpdef
  have hp : 1 ≤ p := by
    have := ENNReal.toReal_mono hqT (Fact.out : (1 : ℝ≥0∞) ≤ q')
    simpa [p] using this
  obtain ⟨d, c, hc⟩ := posSemidef_exists_gram hX
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set y : Fin m → EuclideanSpace ℝ (Fin d) := fun j => ∑ k, G k j • c (Sum.inr k)
  set b : Fin l → EuclideanSpace ℝ (Fin d) := fun i => ∑ k, H k i • c (Sum.inr k)
  set s : Fin m → ℝ := fun j => (SignType.sign ⟪y j, c (Sum.inl j)⟫ : ℝ)
  obtain ⟨hbX, hyX⟩ := aux_zsr_gram G H X c hc
  -- `‖cⱼ‖ ≤ 1` and `(Σᵢ ‖bᵢ‖^p)^{1/p} ≤ 1`
  have hcj : ∀ j, ‖c (Sum.inl j)‖ ≤ 1 := fun j => by
    have h1 : X (Sum.inl j) (Sum.inl j) ≤ 1 := by
      rw [PiLp.norm_toLp] at hX1
      exact (le_abs_self _).trans ((norm_le_pi_norm
        (fun j => X (Sum.inl j) (Sum.inl j)) j).trans hX1)
    rw [hc, real_inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (c (Sum.inl j))]
  have hb : (∑ i, ‖b i‖ ^ p) ^ (1 / p) ≤ 1 := by
    have h := hX2
    simp only [← hbX] at h
    rw [aux_zsr_norm_sq hq'2 hqT (fun i => ‖b i‖)] at h
    have h' : ‖WithLp.toLp q' (fun i => ‖b i‖)‖ ≤ 1 := by
      nlinarith [norm_nonneg (WithLp.toLp q' (fun i => ‖b i‖))]
    rw [PiLp.norm_eq_sum (by positivity)] at h'
    simpa [p] using h'
  -- the rounded functional and its expectation
  set φ : EuclideanSpace ℝ (Fin d) → ℝ := fun g =>
    ∑ j, s j * (⟪y j, g⟫ * (SignType.sign ⟪c (Sum.inl j), g⟫ : ℝ))
  have hcorr := fun j => integral_inner_mul_sign_inner_stdGaussian (y j) (c (Sum.inl j))
  have hφi : Integrable φ μ :=
    integrable_finsetSum _ fun j _ => (hcorr j).1.const_mul (s j)
  have hlow : gaussMomentRoot 1 * ∑ j, ⟪y j, c (Sum.inl j)⟫ ≤ ∫ g, φ g ∂μ := by
    rw [integral_finsetSum _ fun j _ => (hcorr j).1.const_mul (s j), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [integral_const_mul, (hcorr j).2]
    have hγ : 0 < gaussMomentRoot 1 := aux_zsr_gaussMomentRoot_pos
    have hs : s j * (gaussMomentRoot 1 * ⟪y j, c (Sum.inl j)⟫ / ‖c (Sum.inl j)‖) =
        gaussMomentRoot 1 * (|⟪y j, c (Sum.inl j)⟫| / ‖c (Sum.inl j)‖) := by
      rw [← sign_mul_self]; simp only [s]; ring
    rw [hs]
    refine mul_le_mul_of_nonneg_left ?_ hγ.le
    rcases eq_or_lt_of_le (norm_nonneg (c (Sum.inl j))) with h0 | hpos
    · rw [eq_comm, norm_eq_zero] at h0
      simp [h0]
    · exact (le_abs_self _).trans (le_div_self (abs_nonneg _) hpos (hcj j))
  -- the pointwise bound in expectation
  obtain ⟨hFi, hEF⟩ := gaussian_norm_moment_le b zero_lt_one hp
  simp only [Real.rpow_one] at hFi hEF
  have hup : ∫ g, φ g ∂μ ≤ r * gaussMomentRoot p := by
    calc ∫ g, φ g ∂μ ≤ ∫ g, r * (∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p) ∂μ :=
          integral_mono hφi (hFi.const_mul r) fun g =>
            aux_zsr_pointwise q q' hqT G H hH hrle c s (fun j => by
              simp only [s]
              rcases lt_trichotomy ⟪y j, c (Sum.inl j)⟫ 0 with h | h | h <;> simp [h]) g
      _ = r * ∫ g, (∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p) ∂μ := integral_const_mul r _
      _ ≤ r * (gaussMomentRoot p * (∑ i, ‖b i‖ ^ p) ^ (1 / p)) :=
          mul_le_mul_of_nonneg_left hEF hr0
      _ ≤ r * (gaussMomentRoot p * 1) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb ?_) hr0
          exact aux_zsr_gaussMomentRoot_nonneg (by linarith)
      _ = r * gaussMomentRoot p := by rw [mul_one]
  rw [← hyX]
  exact hlow.trans hup


-- =======================================  MAIN THEOREM  ======================================= --

theorem zsr_radius_bounds (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q'] (hq1 : 1 < q)
    (hq2 : q ≤ 2) (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {ZSR r : ℝ}
    (hZSR : IsLeast ((fun vw : (Fin m → ℝ) × (Fin l → ℝ) =>
        (‖WithLp.toLp 1 vw.1‖ + ‖WithLp.toLp (q / (2 - q)) vw.2‖) / 2) ''
        {vw | (fromBlocks 0 Gᵀ G 0 -
          fromBlocks (diagonal vw.1) 0 0 (H * diagonal vw.2 * Hᵀ)).PosSemidef}) ZSR)
    (hr : IsGreatest ((fun α => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
        (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α)) ''
        Metric.closedBall 0 1) r) : -- --- CONCL ---
    r ≤ ZSR ∧ ZSR ≤ gaussMomentRoot q'.toReal / gaussMomentRoot 1 * r ∧
      (ZSR ≤ 1 → ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∃ β : PiLp q (fun _ : Fin l => ℝ),
        H *ᵥ WithLp.ofLp β = G *ᵥ α ∧ ‖β‖ ≤ 1) ∧
      (gaussMomentRoot q'.toReal / gaussMomentRoot 1 < ZSR →
        ∃ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∀ β : PiLp q (fun _ : Fin l => ℝ),
          H *ᵥ WithLp.ofLp β = G *ᵥ α → 1 < ‖β‖) := by -- --- PROOF ---
  haveI : (q / (2 - q)).HolderConjugate (q' / 2) := aux_zsr_holderConjugate hq1 hq2
  haveI : Fact (1 ≤ q / (2 - q)) := ⟨aux_zsr_one_le hq1 hq2⟩
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hrle : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm Hl (G *ᵥ α) ≤ r :=
    fun α hα => hr.2 ⟨α, hα, rfl⟩
  have hr0 : 0 ≤ r := by
    obtain ⟨α, -, hα⟩ := hr.1
    rw [← hα]
    exact coeffNorm_nonneg _ _
  have hγ1 := aux_zsr_gaussMomentRoot_pos
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  have hγp : 0 ≤ gaussMomentRoot q'.toReal := aux_zsr_gaussMomentRoot_nonneg
    (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hqT)
  have hC : 0 ≤ gaussMomentRoot q'.toReal / gaussMomentRoot 1 := div_nonneg hγp hγ1.le
  -- `r ≤ ZSR`
  have hweak : r ≤ ZSR := by
    obtain ⟨⟨v, w⟩, hvw, hZ⟩ := hZSR.1
    obtain ⟨α, hα, hαr⟩ := hr.1
    rw [← hZ, ← hαr]
    exact aux_zsr_weak q q' hq1 hq2 G H hH v w hvw hα
  -- `ZSR ≤ (γ_{q*}/γ₁) r`: every `t ∈ (0, ZSR)` is at most it
  have hup : ZSR ≤ gaussMomentRoot q'.toReal / gaussMomentRoot 1 * r := by
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    rcases le_or_gt t 0 with ht0 | ht0
    · exact ht0.trans (mul_nonneg hC hr0)
    obtain ⟨X, hX, hX1, hX2, hXt⟩ := diag_block_sdp_exists_dual 1 ∞ (q / (2 - q)) (q' / 2) G H
      hH ht0 fun v w h => ht.trans_le (hZSR.2 ⟨(v, w), h, rfl⟩)
    have hround := aux_zsr_rounding q q' hq1 hq2 G H hH hr0 hrle X hX hX1 hX2
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ1]
    nlinarith
  refine ⟨hweak, hup, fun h1 α hα => ?_, fun hlt => ?_⟩
  · obtain ⟨β, hβ, hβn⟩ := (coeffNorm_le_iff Hl (x := G *ᵥ α) (by
      obtain ⟨b, hb⟩ := hH (G *ᵥ α)
      exact ⟨WithLp.toLp q b, hb⟩)).mp ((hrle α hα).trans (hweak.trans h1))
    exact ⟨β, hβ, hβn⟩
  · -- `C < ZSR ≤ C r` forces `r > 1`, and the maximizer leaves `E_q(H)`
    have h1 : 1 < r := by
      have : gaussMomentRoot q'.toReal / gaussMomentRoot 1 * 1 <
          gaussMomentRoot q'.toReal / gaussMomentRoot 1 * r := by
        rw [mul_one]; exact hlt.trans_le hup
      exact lt_of_mul_lt_mul_left this hC
    obtain ⟨α, hα, hαr⟩ := hr.1
    refine ⟨α, hα, fun β hβ => ?_⟩
    have : coeffNorm Hl (G *ᵥ α) ≤ ‖β‖ := by
      rw [← hβ]
      exact coeffNorm_le Hl β
    simp only at hαr
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
