module

public import CORALean.Global.CoeffNormLeDual
public import CORALean.Global.DiagBlockSdpDual
public import CORALean.Global.DotProductLeCoeffNorm
public import CORALean.Global.GaussianNormMomentLe
public import CORALean.Global.PosSemidefGram
public import CORALean.Global.SdpRelaxationQuadLe
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# The semidefinite relaxation of ellipsotope-in-ellipsotope containment

[1, Thm. 19]: for `1 < q ≤ 2 ≤ p < ∞` and `H` onto, `SR_{p,q} = ½ min_K (‖v‖_{p/(p-2)} +
‖w‖_{q*/(q*-2)})` (Eq. 41), `K` the `(v, w)` with `[Diag(v), 0; 0, H Diag(w) Hᵀ] ≼ [0, Gᵀ; G, 0]`
(Eq. 42), has `r ≤ SR_{p,q} ≤ γ_{q*} γ_p r` (Eq. 43), `r` the greatest `coeffNorm H` over the
`p`-ball and `γ_k` the constant of Eq. 31. The minimum exists (`sdp_relaxation_exists_isLeast`); at
`x = 2` the exponent `x/(x-2)` is `∞`. The paper cites Thm. 5.4 of its reference 22; here duality
and rounding are written out: `r ≤ SR_{p,q}` as for `zsr_radius_bounds`; for the upper bound a
certificate `X ≽ 0` (`diag_block_sdp_exists_dual`), rounded at a standard Gaussian as a Gram matrix,
gives `ζᵀ G α ≤ r ‖α‖_p ‖Hᵀ ζ‖_{q*}`, bounded by Hölder and `gaussian_norm_moment_le`.

## Inputs
* `p` – exponent of the inner coefficient norm
* `q` – exponent of the outer coefficient norm
* `q'` – its conjugate exponent
* `G` – generator matrix of the inner set
* `H` – generator matrix of the outer set
* `SR` – relaxation value
* `r` – containment radius

## Hypotheses
* `hq1` – the outer exponent exceeds one
* `hq2` – the outer exponent is at most two
* `hp2` – the inner exponent is at least two
* `hpT` – the inner exponent is finite
* `hH` – the outer generator matrix is onto
* `hSR` – the relaxation value is the least feasible one
* `hr` – the radius is the greatest norm over the unit ball

## Conclusion
* the radius is at most the relaxation value, which is at most a Gaussian constant times the radius

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
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

/-- `x / (x - 2)` and `x / 2` are Hölder conjugates for `2 ≤ x < ∞`. -/
private theorem aux_sr_holderConjugate {x : ℝ≥0∞} (hx : 2 ≤ x) (hxT : x ≠ ∞) :
    (x / (x - 2)).HolderConjugate (x / 2) := by
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by norm_num) hx).ne'
  rw [ENNReal.holderConjugate_iff, ENNReal.inv_div (Or.inl (ENNReal.sub_ne_top hxT))
    (Or.inr hx0), ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp)),
    ENNReal.div_add_div_same, tsub_add_cancel_of_le hx, ENNReal.div_self hx0 hxT]

/-- `‖(tᵢ²)ᵢ‖_{x/2} = ‖t‖_x²` for `2 ≤ x < ∞`. -/
private theorem aux_sr_norm_sq {k : ℕ} {x : ℝ≥0∞} (hx : 2 ≤ x) (hxT : x ≠ ∞)
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

/-- `q* ≥ 2` for `q ≤ 2`. -/
private theorem aux_sr_two_le_conj {q q' : ℝ≥0∞} [q.HolderConjugate q'] (hq2 : q ≤ 2) : 2 ≤ q' := by
  rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv q q', ← ENNReal.one_sub_inv_two]
  exact tsub_le_tsub_left (ENNReal.inv_le_inv.mpr hq2) 1

private theorem aux_sr_gaussMomentRoot_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ gaussMomentRoot p := by
  unfold gaussMomentRoot
  exact Real.rpow_nonneg (mul_nonneg (by positivity)
    (Real.Gamma_pos_of_pos (by linarith)).le) _

/-- `E[⟨a, g⟩ ⟨b, g⟩] = ⟨a, b⟩`, the covariance of the standard Gaussian. -/
private theorem aux_sr_integral_inner_mul_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a b : E) : -- --- CONCL ---
    Integrable (fun g => ⟪a, g⟫ * ⟪b, g⟫) (stdGaussian E) ∧
      ∫ g, ⟪a, g⟫ * ⟪b, g⟫ ∂(stdGaussian E) = ⟪a, b⟫ := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · have ha := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ a) 2 (by simp)
    have hb := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ b) 2 (by simp)
    exact ha.integrable_mul hb
  · have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id a b
    rw [covarianceBilin_stdGaussian] at h
    have h0 : ∫ x, id x ∂(stdGaussian E) = 0 := integral_id_stdGaussian
    simp only [h0, sub_zero] at h
    exact h.symm.trans (innerSL_apply_apply (𝕜 := ℝ) a b)

/-- The radius is homogeneous: `‖G α‖_{E_q(H)} ≤ r ‖α‖_p`. -/
private theorem aux_sr_homogeneous (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {r : ℝ}
    (hrle : ∀ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
      coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
        (G *ᵥ WithLp.ofLp α) ≤ r)
    (α : PiLp p (fun _ : Fin m => ℝ)) : -- --- CONCL ---
    coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
      (G *ᵥ WithLp.ofLp α) ≤ r * ‖α‖ := by -- --- PROOF ---
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hpre : ∀ x, ∃ β, Hl β = x := fun x => by
    obtain ⟨b, hb⟩ := hH x
    exact ⟨WithLp.toLp q b, hb⟩
  rcases eq_or_ne α 0 with rfl | hα
  · simp [coeffNorm_zero]
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h := hrle (‖α‖⁻¹ • α) (by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne'])
  rw [WithLp.ofLp_smul, mulVec_smul, coeffNorm_smul Hl (hpre _), abs_inv, abs_of_pos hn] at h
  rw [inv_mul_le_iff₀ hn] at h
  linarith

/-- The weak half: a pair of `K` bounds the norm of every point of `E_p(G)`. -/
private theorem aux_sr_weak (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate q']
    (hq1 : 1 < q) (hq2 : q ≤ 2) (hp2 : 2 ≤ p) (hpT : p ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (hH : Function.Surjective H.mulVec) (v : Fin m → ℝ)
    (w : Fin l → ℝ)
    (hK : (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)).PosSemidef)
    {α : PiLp p (fun _ : Fin m => ℝ)} (hα : α ∈ Metric.closedBall 0 1) : -- --- CONCL ---
    coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
      (G *ᵥ WithLp.ofLp α) ≤
        (‖WithLp.toLp (p / (p - 2)) v‖ + ‖WithLp.toLp (q' / (q' - 2)) w‖) / 2 := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  have hq'2 := aux_sr_two_le_conj (q' := q') hq2
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  haveI := aux_sr_holderConjugate hp2 hpT
  haveI := aux_sr_holderConjugate hq'2 hqT
  haveI : Fact (1 ≤ p / (p - 2)) := ⟨ENNReal.HolderConjugate.one_le (p / (p - 2)) (p / 2)⟩
  haveI : Fact (1 ≤ q' / (q' - 2)) := ⟨ENNReal.HolderConjugate.one_le (q' / (q' - 2)) (q' / 2)⟩
  haveI : Fact (1 ≤ p / 2) := ⟨ENNReal.HolderConjugate.one_le (p / 2) (p / (p - 2))⟩
  haveI : Fact (1 ≤ q' / 2) := ⟨ENNReal.HolderConjugate.one_le (q' / 2) (q' / (q' - 2))⟩
  -- a dual vector attains the norm of `G α`; the matrix inequality at `(α, -z)` bounds it
  obtain ⟨z, hz, hle⟩ := exists_dual_coeffNorm_le q q' H (hH (G *ᵥ WithLp.ofLp α))
  have hq := sdp_relaxation_quad_le (p / (p - 2)) (p / 2) (q' / (q' - 2)) (q' / 2) G H v w hK
    (WithLp.ofLp α) z
  -- `‖α²‖_{p/2} = ‖α‖_p² ≤ 1` and `‖(Hᵀ z)²‖_{q*/2} = ‖Hᵀ z‖_{q*}² ≤ 1`
  have hα2 : ‖WithLp.toLp (p / 2) (fun j => WithLp.ofLp α j ^ 2)‖ ≤ 1 := by
    rw [aux_sr_norm_sq hp2 hpT, WithLp.toLp_ofLp]
    exact pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hα)
  have hz2 : ‖WithLp.toLp (q' / 2) (fun i => (z ᵥ* H) i ^ 2)‖ ≤ 1 := by
    rw [aux_sr_norm_sq hq'2 hqT]
    exact pow_le_one₀ (norm_nonneg _) hz
  have h1 := mul_le_mul_of_nonneg_left hα2 (norm_nonneg (WithLp.toLp (p / (p - 2)) v))
  have h2 := mul_le_mul_of_nonneg_left hz2 (norm_nonneg (WithLp.toLp (q' / (q' - 2)) w))
  linarith

/-- The pointwise bound of the rounding: `ζᵀ G α ≤ r ‖α‖_p ‖Hᵀ ζ‖_{q*}` with the Gaussian
images `αⱼ = ⟨cⱼ, g⟩`, `ζₖ = ⟨cₖ, g⟩`. -/
private theorem aux_sr_pointwise {d : ℕ} (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [q.HolderConjugate q'] (hpT : p ≠ ∞) (hq' : q' ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (hH : Function.Surjective H.mulVec) {r : ℝ}
    (hrle : ∀ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
      coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
        (G *ᵥ WithLp.ofLp α) ≤ r)
    (c : Fin m ⊕ Fin n → EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d)) : -- --- CONCL ---
    ∑ k, ∑ j, G k j * (⟪c (Sum.inr k), g⟫ * ⟪c (Sum.inl j), g⟫) ≤
      r * ((∑ j, |⟪c (Sum.inl j), g⟫| ^ p.toReal) ^ (1 / p.toReal) *
        (∑ i, |⟪∑ k, H k i • c (Sum.inr k), g⟫| ^ q'.toReal) ^
          (1 / q'.toReal)) := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpT
  have hq0 : 0 < q'.toReal := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'
  -- the rounded vectors `ζ`, `α` and their norms
  set ζ : Fin n → ℝ := fun k => ⟪c (Sum.inr k), g⟫
  set α : Fin m → ℝ := fun j => ⟪c (Sum.inl j), g⟫
  have hL : ∑ k, ∑ j, G k j * (⟪c (Sum.inr k), g⟫ * ⟪c (Sum.inl j), g⟫) = ζ ⬝ᵥ (G *ᵥ α) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ζ, α]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ‖WithLp.toLp p α‖ = (∑ j, |⟪c (Sum.inl j), g⟫| ^ p.toReal) ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum (by simpa using hp0)]
    simp [α, Real.norm_eq_abs]
  have hB : ‖WithLp.toLp q' (ζ ᵥ* H)‖ =
      (∑ i, |⟪∑ k, H k i • c (Sum.inr k), g⟫| ^ q'.toReal) ^ (1 / q'.toReal) := by
    rw [PiLp.norm_eq_sum (by simpa using hq0)]
    simp only [vecMul, dotProduct, sum_inner, real_inner_smul_left, Real.norm_eq_abs, ζ]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      congr 2; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- `ζᵀ G α ≤ ‖G α‖ ‖Hᵀ ζ‖_{q*} ≤ r ‖α‖_p ‖Hᵀ ζ‖_{q*}`
  rw [hL, ← hA, ← hB]
  have h := aux_sr_homogeneous p q G H hH hrle (WithLp.toLp p α)
  rw [WithLp.ofLp_toLp] at h
  calc ζ ⬝ᵥ (G *ᵥ α) ≤ _ := dotProduct_le_coeffNorm_mul_norm q q' H (hH _) ζ
    _ ≤ r * ‖WithLp.toLp p α‖ * ‖WithLp.toLp q' (ζ ᵥ* H)‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := mul_assoc _ _ _

/-- Hölder and the moment bounds: `E[A B] ≤ γ_p γ_{q*}` for the two rounded norms. -/
private theorem aux_sr_expect_le {d : ℕ} {P Q : ℝ} (hP : 2 ≤ P) (hQ : 2 ≤ Q)
    (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin l → EuclideanSpace ℝ (Fin d))
    (ha : (∑ j, ‖a j‖ ^ P) ^ (1 / P) ≤ 1) (hb : (∑ i, ‖b i‖ ^ Q) ^ (1 / Q) ≤ 1) : -- --- CONCL ---
    Integrable (fun g => (∑ j, |⟪a j, g⟫| ^ P) ^ (1 / P) * (∑ i, |⟪b i, g⟫| ^ Q) ^ (1 / Q))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
    ∫ g, (∑ j, |⟪a j, g⟫| ^ P) ^ (1 / P) * (∑ i, |⟪b i, g⟫| ^ Q) ^ (1 / Q)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        gaussMomentRoot P * gaussMomentRoot Q := by -- --- PROOF ---
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set A : EuclideanSpace ℝ (Fin d) → ℝ := fun g => (∑ j, |⟪a j, g⟫| ^ P) ^ (1 / P)
  set B : EuclideanSpace ℝ (Fin d) → ℝ := fun g => (∑ i, |⟪b i, g⟫| ^ Q) ^ (1 / Q)
  -- the Hölder conjugate `P' = P/(P-1)` of `P` is at most `2 ≤ Q`
  have hP1 : 1 < P := by linarith
  set P' := Real.conjExponent P
  have hPP' : P.HolderConjugate P' := Real.HolderConjugate.conjExponent hP1
  have hP'2 : P' ≤ Q := by
    have : P' ≤ 2 := by
      simp only [P', Real.conjExponent]
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hP'0 : 0 < P' := hPP'.symm.pos
  have hA0 : ∀ g, 0 ≤ A g := fun g => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by
    positivity) _
  have hB0 : ∀ g, 0 ≤ B g := fun g => Real.rpow_nonneg (Finset.sum_nonneg fun i _ => by
    positivity) _
  -- the moments of `A` and `B`, and `A ∈ L^P`, `B ∈ L^{P'}`
  obtain ⟨hAi, hAE⟩ := gaussian_norm_moment_le a (by linarith : (0 : ℝ) < P) le_rfl
  obtain ⟨hBi, hBE⟩ := gaussian_norm_moment_le b hP'0 hP'2
  have hAc : Continuous A :=
    (continuous_finsetSum _ fun j _ => ((continuous_const.inner continuous_id).abs).rpow_const
      fun _ => Or.inr (by linarith)).rpow_const fun _ => Or.inr (by positivity)
  have hBc : Continuous B :=
    (continuous_finsetSum _ fun i _ => ((continuous_const.inner continuous_id).abs).rpow_const
      fun _ => Or.inr (by linarith)).rpow_const fun _ => Or.inr (by positivity)
  have hAm : MemLp A (ENNReal.ofReal P) μ := by
    rw [← integrable_norm_rpow_iff hAc.aestronglyMeasurable (by simp; linarith) (by simp),
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ P)]
    refine hAi.congr (ae_of_all _ fun g => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hA0 g)]
    rfl
  have hBm : MemLp B (ENNReal.ofReal P') μ := by
    rw [← integrable_norm_rpow_iff hBc.aestronglyMeasurable (by simp; linarith) (by simp),
      ENNReal.toReal_ofReal hP'0.le]
    refine hBi.congr (ae_of_all _ fun g => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hB0 g)]
    rfl
  -- Hölder: `E[A B] ≤ (E A^P)^{1/P} (E B^{P'})^{1/P'}`
  haveI : (ENNReal.ofReal P).HolderConjugate (ENNReal.ofReal P') := hPP'.ennrealOfReal
  refine ⟨hAm.integrable_mul hBm, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hPP' (ae_of_all _ hA0) (ae_of_all _ hB0) hAm hBm
  -- the constants are nonnegative
  have hγP := aux_sr_gaussMomentRoot_nonneg (by linarith : (0 : ℝ) < P)
  have hγQ := aux_sr_gaussMomentRoot_nonneg (by linarith : (0 : ℝ) < Q)
  -- `(E A^P)^{1/P} ≤ γ_P` and `(E B^{P'})^{1/P'} ≤ γ_Q`
  have h1 : (∫ g, A g ^ P ∂μ) ^ (1 / P) ≤ gaussMomentRoot P := by
    calc (∫ g, A g ^ P ∂μ) ^ (1 / P)
        ≤ ((gaussMomentRoot P * (∑ j, ‖a j‖ ^ P) ^ (1 / P)) ^ P) ^ (1 / P) :=
          Real.rpow_le_rpow (integral_nonneg fun g => by have := hA0 g; positivity) hAE
            (by positivity)
      _ = gaussMomentRoot P * (∑ j, ‖a j‖ ^ P) ^ (1 / P) := by
          rw [show 1 / P = P⁻¹ from one_div P, Real.rpow_rpow_inv (by positivity) (by linarith)]
      _ ≤ gaussMomentRoot P * 1 := mul_le_mul_of_nonneg_left ha hγP
      _ = gaussMomentRoot P := mul_one _
  -- the same for `B` at `P' ≤ Q`
  have h2 : (∫ g, B g ^ P' ∂μ) ^ (1 / P') ≤ gaussMomentRoot Q := by
    calc (∫ g, B g ^ P' ∂μ) ^ (1 / P')
        ≤ ((gaussMomentRoot Q * (∑ i, ‖b i‖ ^ Q) ^ (1 / Q)) ^ P') ^ (1 / P') :=
          Real.rpow_le_rpow (integral_nonneg fun g => by have := hB0 g; positivity) hBE
            (by positivity)
      _ = gaussMomentRoot Q * (∑ i, ‖b i‖ ^ Q) ^ (1 / Q) := by
          rw [show 1 / P' = P'⁻¹ from one_div P', Real.rpow_rpow_inv (by positivity) hP'0.ne']
      _ ≤ gaussMomentRoot Q * 1 := mul_le_mul_of_nonneg_left hb hγQ
      _ = gaussMomentRoot Q := mul_one _
  calc ∫ g, A g * B g ∂μ ≤ _ := hH
    _ ≤ gaussMomentRoot P * gaussMomentRoot Q :=
        mul_le_mul h1 h2 (by positivity) hγP

/-- The Gram vectors: `‖Σₖ H_{ki} cₖ‖² = (Hᵀ X₂₂ H)ᵢᵢ`. -/
private theorem aux_sr_gram {d : ℕ} (H : Matrix (Fin n) (Fin l) ℝ)
    (X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
    (c : Fin m ⊕ Fin n → EuclideanSpace ℝ (Fin d)) (hc : ∀ p q, X p q = ⟪c p, c q⟫)
    (i : Fin l) : -- --- CONCL ---
    ‖∑ k, H k i • c (Sum.inr k)‖ ^ 2 = (Hᵀ * X.toBlocks₂₂ * H) i i := by -- --- PROOF ---
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, ← hc, mul_apply,
    transpose_apply, toBlocks₂₂, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring

/-- A family whose squared norms have `x/2`-norm at most `1` has `(Σ ‖·‖^x)^{1/x} ≤ 1`. -/
private theorem aux_sr_family_le_one {d k : ℕ} {x : ℝ≥0∞} (hx : 2 ≤ x) (hxT : x ≠ ∞)
    (a : Fin k → EuclideanSpace ℝ (Fin d))
    (h : ‖WithLp.toLp (x / 2) (fun i => ‖a i‖ ^ 2)‖ ≤ 1) : -- --- CONCL ---
    (∑ i, ‖a i‖ ^ x.toReal) ^ (1 / x.toReal) ≤ 1 := by -- --- PROOF ---
  haveI : Fact (1 ≤ x) := ⟨le_trans (by norm_num) hx⟩
  rw [aux_sr_norm_sq hx hxT (fun i => ‖a i‖)] at h
  have h' : ‖WithLp.toLp x (fun i => ‖a i‖)‖ ≤ 1 := by
    nlinarith [norm_nonneg (WithLp.toLp x (fun i => ‖a i‖))]
  have h0 : 0 < x.toReal := ENNReal.toReal_pos (lt_of_lt_of_le (by norm_num) hx).ne' hxT
  rw [PiLp.norm_eq_sum h0] at h'
  simpa using h'

/-- The rounding: a certificate `X` gives `Σ G_{kj} X_{kj} ≤ r γ_p γ_{q*}`. -/
private theorem aux_sr_rounding (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate q']
    (hq1 : 1 < q) (hq2 : q ≤ 2) (hp2 : 2 ≤ p) (hpT : p ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (hH : Function.Surjective H.mulVec) {r : ℝ} (hr0 : 0 ≤ r)
    (hrle : ∀ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
      coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap)
        (G *ᵥ WithLp.ofLp α) ≤ r)
    (X : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (hX : X.PosSemidef)
    (hX1 : ‖WithLp.toLp (p / 2) (fun j => X (Sum.inl j) (Sum.inl j))‖ ≤ 1)
    (hX2 : ‖WithLp.toLp (q' / 2) (fun i => (Hᵀ * X.toBlocks₂₂ * H) i i)‖ ≤ 1) : -- --- CONCL ---
    ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) ≤
      r * (gaussMomentRoot p.toReal * gaussMomentRoot q'.toReal) := by -- --- PROOF ---
  have hq'2 := aux_sr_two_le_conj (q' := q') hq2
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  have hP : 2 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpT hp2
    simpa using this
  have hQ : 2 ≤ q'.toReal := by
    have := ENNReal.toReal_mono hqT hq'2
    simpa using this
  -- `X` as a Gram matrix; `(Σ ‖aⱼ‖^p)^{1/p} ≤ 1` and `(Σ ‖bᵢ‖^{q*})^{1/q*} ≤ 1`
  obtain ⟨d, c, hc⟩ := posSemidef_exists_gram hX
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set a : Fin m → EuclideanSpace ℝ (Fin d) := fun j => c (Sum.inl j)
  set b : Fin l → EuclideanSpace ℝ (Fin d) := fun i => ∑ k, H k i • c (Sum.inr k)
  have ha : (∑ j, ‖a j‖ ^ p.toReal) ^ (1 / p.toReal) ≤ 1 := by
    refine aux_sr_family_le_one hp2 hpT a ?_
    convert hX1 using 3
    simp [a, hc]
  have hb : (∑ i, ‖b i‖ ^ q'.toReal) ^ (1 / q'.toReal) ≤ 1 := by
    refine aux_sr_family_le_one hq'2 hqT b ?_
    convert hX2 using 3
    funext i
    exact aux_sr_gram H X c hc i
  obtain ⟨hABi, hAB⟩ := aux_sr_expect_le hP hQ a b ha hb
  -- the rounded bilinear form and its expectation
  set φ : EuclideanSpace ℝ (Fin d) → ℝ := fun g =>
    ∑ k, ∑ j, G k j * (⟪c (Sum.inr k), g⟫ * ⟪c (Sum.inl j), g⟫)
  have hcov := fun k j => aux_sr_integral_inner_mul_inner (c (Sum.inr k)) (c (Sum.inl j))
  have hφi : Integrable φ μ := integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => (hcov k j).1.const_mul (G k j)
  have hEφ : ∫ g, φ g ∂μ = ∑ k, ∑ j, G k j * X (Sum.inr k) (Sum.inl j) := by
    rw [integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun j _ => (hcov k j).1.const_mul (G k j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun j _ => (hcov k j).1.const_mul (G k j)]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, (hcov k j).2, hc]
  rw [← hEφ]
  calc ∫ g, φ g ∂μ ≤ ∫ g, r * ((∑ j, |⟪a j, g⟫| ^ p.toReal) ^ (1 / p.toReal) *
        (∑ i, |⟪b i, g⟫| ^ q'.toReal) ^ (1 / q'.toReal)) ∂μ :=
        integral_mono hφi (hABi.const_mul r) fun g =>
          aux_sr_pointwise p q q' hpT hqT G H hH hrle c g
    _ = r * ∫ g, (∑ j, |⟪a j, g⟫| ^ p.toReal) ^ (1 / p.toReal) *
        (∑ i, |⟪b i, g⟫| ^ q'.toReal) ^ (1 / q'.toReal) ∂μ := integral_const_mul r _
    _ ≤ _ := mul_le_mul_of_nonneg_left hAB hr0


-- =======================================  MAIN THEOREM  ======================================= --

theorem sr_radius_bounds (p q q' : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate q']
    (hq1 : 1 < q) (hq2 : q ≤ 2) (hp2 : 2 ≤ p) (hpT : p ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (hH : Function.Surjective H.mulVec) {SR r : ℝ}
    (hSR : IsLeast ((fun vw : (Fin m → ℝ) × (Fin l → ℝ) =>
        (‖WithLp.toLp (p / (p - 2)) vw.1‖ + ‖WithLp.toLp (q' / (q' - 2)) vw.2‖) / 2) ''
        {vw | (fromBlocks 0 Gᵀ G 0 -
          fromBlocks (diagonal vw.1) 0 0 (H * diagonal vw.2 * Hᵀ)).PosSemidef}) SR)
    (hr : IsGreatest ((fun α : PiLp p (fun _ : Fin m => ℝ) => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
        (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ WithLp.ofLp α)) ''
        Metric.closedBall 0 1) r) : -- --- CONCL ---
    r ≤ SR ∧ SR ≤ gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal * r ∧
      (SR ≤ 1 → ∀ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
        ∃ β : PiLp q (fun _ : Fin l => ℝ), H *ᵥ WithLp.ofLp β = G *ᵥ WithLp.ofLp α ∧ ‖β‖ ≤ 1) ∧
      (gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal < SR →
        ∃ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
          ∀ β : PiLp q (fun _ : Fin l => ℝ), H *ᵥ WithLp.ofLp β = G *ᵥ WithLp.ofLp α →
            1 < ‖β‖) := by -- --- PROOF ---
  have hq'2 := aux_sr_two_le_conj (q' := q') hq2
  have hqT : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1.ne'
  haveI := aux_sr_holderConjugate hp2 hpT
  haveI := aux_sr_holderConjugate hq'2 hqT
  haveI : Fact (1 ≤ p / (p - 2)) := ⟨ENNReal.HolderConjugate.one_le (p / (p - 2)) (p / 2)⟩
  haveI : Fact (1 ≤ q' / (q' - 2)) := ⟨ENNReal.HolderConjugate.one_le (q' / (q' - 2)) (q' / 2)⟩
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hrle : ∀ α ∈ Metric.closedBall (0 : PiLp p (fun _ : Fin m => ℝ)) 1,
      coeffNorm Hl (G *ᵥ WithLp.ofLp α) ≤ r := fun α hα => hr.2 ⟨α, hα, rfl⟩
  have hr0 : 0 ≤ r := by
    obtain ⟨α, -, hα⟩ := hr.1
    rw [← hα]
    exact coeffNorm_nonneg _ _
  have hγp := aux_sr_gaussMomentRoot_nonneg
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpT)
  have hγq := aux_sr_gaussMomentRoot_nonneg
    (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hqT)
  have hC : 0 ≤ gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal := mul_nonneg hγq hγp
  -- `r ≤ SR`
  have hweak : r ≤ SR := by
    obtain ⟨⟨v, w⟩, hvw, hZ⟩ := hSR.1
    obtain ⟨α, hα, hαr⟩ := hr.1
    rw [← hZ, ← hαr]
    exact aux_sr_weak p q q' hq1 hq2 hp2 hpT G H hH v w hvw hα
  -- `SR ≤ γ_{q*} γ_p r`: every `t ∈ (0, SR)` is at most it
  have hup : SR ≤ gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal * r := by
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    rcases le_or_gt t 0 with ht0 | ht0
    · exact ht0.trans (mul_nonneg hC hr0)
    obtain ⟨X, hX, hX1, hX2, hXt⟩ := diag_block_sdp_exists_dual (p / (p - 2)) (p / 2)
      (q' / (q' - 2)) (q' / 2) G H hH ht0 fun v w h => ht.trans_le (hSR.2 ⟨(v, w), h, rfl⟩)
    have hround := aux_sr_rounding p q q' hq1 hq2 hp2 hpT G H hH hr0 hrle X hX hX1 hX2
    linarith [mul_comm (gaussMomentRoot p.toReal) (gaussMomentRoot q'.toReal),
      mul_comm r (gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal)]
  refine ⟨hweak, hup, fun h1 α hα => ?_, fun hlt => ?_⟩
  · obtain ⟨β, hβ, hβn⟩ := (coeffNorm_le_iff Hl (x := G *ᵥ WithLp.ofLp α) (by
      obtain ⟨b, hb⟩ := hH (G *ᵥ WithLp.ofLp α)
      exact ⟨WithLp.toLp q b, hb⟩)).mp ((hrle α hα).trans (hweak.trans h1))
    exact ⟨β, hβ, hβn⟩
  · -- `C < SR ≤ C r` forces `r > 1`, and the maximizer leaves `E_q(H)`
    have h1 : 1 < r := by
      have : gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal * 1 <
          gaussMomentRoot q'.toReal * gaussMomentRoot p.toReal * r := by
        rw [mul_one]; exact hlt.trans_le hup
      exact lt_of_mul_lt_mul_left this hC
    obtain ⟨α, hα, hαr⟩ := hr.1
    refine ⟨α, hα, fun β hβ => ?_⟩
    have : coeffNorm Hl (G *ᵥ WithLp.ofLp α) ≤ ‖β‖ := by
      rw [← hβ]
      exact coeffNorm_le Hl β
    simp only at hαr
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
