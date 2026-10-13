module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.DotProductLeCoeffNorm
public import CORALean.Global.GaussianRoundingLe
public import CORALean.Global.LinearRelaxationDual
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The accuracy of the linear relaxation

[1, Thm. 15 (accuracy)]: for `H` surjective and `q ∈ (1, ∞]`,
`LR_q(G, H) ≤ (γ_{q*} √m / γ₁) r(Z(G), E_q(H))` (the second inequality of Eq. 30), `γ_k` the
constant of Eq. 31 (`gaussMomentRoot`); so `LR_q > γ_{q*} √m / γ₁` gives a point of `Z(G)`
outside `E_q(H)`. `LR_q` is the minimum of Eq. 29 and `r` the maximum over the cube of the
ellipsotope norm `coeffNorm H`, as in `lr_isLeast_radius_le`. At `q = 1` the constant `γ_∞` of
Eq. 31 is not a number, so `q* = q'` is finite here.

The paper's proof cites Thm. 5.9 of its reference 22; the argument here is its Gaussian
rounding, written out. A dual certificate `Y` with `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1` and
`tr(Gᵀ Y) ≥ LR_q` exists (`lr_exists_dual`). For every `z`, `‖Gᵀ z‖₁ = zᵀ G σ ≤ r ‖Hᵀ z‖_{q*}`
with `σ` the signs of `Gᵀ z` (`dotProduct_le_coeffNorm_mul_norm`, the dual form Eq. 21). At
`z = Y g`, `g` a standard Gaussian vector in `ℝ^m`, the rows `aₖ` of `Gᵀ Y` and `bᵢ` of `Hᵀ Y`
give `Σₖ |⟨aₖ, g⟩| ≤ r ‖(⟨bᵢ, g⟩)ᵢ‖_{q*}`, and `gaussian_rounding_le` turns it into
`γ₁ Σₖ ‖aₖ‖ ≤ r γ_{q*} (Σᵢ ‖bᵢ‖^{q*})^{1/q*}`. On the left `tr(Gᵀ Y) ≤ Σₖ ‖aₖ‖`; on the right
`‖bᵢ‖ ≤ √m maxⱼ |(Hᵀ Y)ᵢⱼ|`, so the root is at most `√m ‖Hᵀ Y‖_{L⊤∞,q*} ≤ √m`.

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

open scoped ENNReal NNReal RealInnerProductSpace
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dual form (Eq. 21) as an inequality: `‖Gᵀ z‖₁ ≤ r ‖Hᵀ z‖_{q*}`. -/
theorem aux_lrAcc_dual_bound (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {r : ℝ}
    (hr : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm ((Matrix.mulVecLin H) ∘ₗ
      (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α) ≤ r)
    (z : Fin n → ℝ) :
    ∑ k, |(z ᵥ* G) k| ≤ r * ‖WithLp.toLp q' (z ᵥ* H)‖ := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  set σ : Fin m → ℝ := fun k => (SignType.sign ((z ᵥ* G) k) : ℝ)
  have hσ : σ ∈ Metric.closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
    simp only [σ, Real.norm_eq_abs]
    rcases lt_trichotomy ((z ᵥ* G) k) 0 with h | h | h <;> simp [h]
  calc ∑ k, |(z ᵥ* G) k| = z ⬝ᵥ (G *ᵥ σ) := by
        rw [dotProduct_mulVec]
        simp only [dotProduct, σ]
        exact Finset.sum_congr rfl fun k _ => (self_mul_sign _).symm
    _ ≤ coeffNorm Hl (G *ᵥ σ) * ‖WithLp.toLp q' (z ᵥ* H)‖ :=
        dotProduct_le_coeffNorm_mul_norm q q' H (hH _) z
    _ ≤ r * ‖WithLp.toLp q' (z ᵥ* H)‖ :=
        mul_le_mul_of_nonneg_right (hr σ hσ) (norm_nonneg _)

/-- A row's Euclidean norm is at most `√m` times its largest entry. -/
theorem aux_lrAcc_norm_le_sqrt_mul (v : Fin m → ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ Real.sqrt m * ⨆ j, |v j| := by -- --- PROOF ---
  have hM : ∀ j, |v j| ≤ ⨆ j, |v j| := fun j =>
    le_ciSup (f := fun j => |v j|) (Set.finite_range _).bddAbove j
  have hM0 : 0 ≤ ⨆ j, |v j| := Real.iSup_nonneg fun j => abs_nonneg _
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hM0, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)) j‖ ^ 2
      ≤ ∑ _j : Fin m, (⨆ j, |v j|) ^ 2 := Finset.sum_le_sum fun j _ => by
        simp only [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM j) 2
    _ = m * (⨆ j, |v j|) ^ 2 := by simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_le_gaussMomentRoot_mul_radius (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (hq' : q' ≠ ∞) (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ)
    (hH : Function.Surjective H.mulVec) {LR r : ℝ}
    (hLR : IsLeast {N | ∃ X : Matrix (Fin l) (Fin m) ℝ, H * X = G ∧
        N = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖} LR)
    (hr : IsGreatest ((fun α => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
        (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α)) ''
        Metric.closedBall 0 1) r) :
    LR ≤ gaussMomentRoot q'.toReal * Real.sqrt m / gaussMomentRoot 1 * r ∧
      (gaussMomentRoot q'.toReal * Real.sqrt m / gaussMomentRoot 1 < LR →
        ∃ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∀ β : PiLp q (fun _ : Fin l => ℝ),
          H *ᵥ WithLp.ofLp β = G *ᵥ α → 1 < ‖β‖) := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  set p := q'.toReal
  have hp : 1 ≤ p := by
    have := ENNReal.toReal_mono hq' (Fact.out : (1 : ℝ≥0∞) ≤ q')
    simpa [p] using this
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hrle : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm Hl (G *ᵥ α) ≤ r :=
    fun α hα => hr.2 ⟨α, hα, rfl⟩
  have hr0 : 0 ≤ r := by
    obtain ⟨α, -, hα⟩ := hr.1
    rw [← hα]
    exact coeffNorm_nonneg _ _
  -- a dual certificate
  have hG : ∃ X₀ : Matrix (Fin l) (Fin m) ℝ, H * X₀ = G := by
    choose c hc using fun j : Fin m => hH (fun k => G k j)
    refine ⟨Matrix.of fun i j => c j i, ?_⟩
    ext k j
    have := congrFun (hc j) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  obtain ⟨LR', hLR', Y, hY, hLRY⟩ := lr_exists_dual q q' G H hG
  rw [← hLR.unique hLR'] at hLRY
  -- the rows of `Gᵀ Y` and `Hᵀ Y`
  set a : Fin m → EuclideanSpace ℝ (Fin m) := fun k => WithLp.toLp 2 fun j => (Gᵀ * Y) k j
  set b : Fin l → EuclideanSpace ℝ (Fin m) := fun i => WithLp.toLp 2 fun j => (Hᵀ * Y) i j
  have hpt : ∀ g : EuclideanSpace ℝ (Fin m),
      ∑ k, |⟪a k, g⟫| ≤ r * (∑ i, |⟪b i, g⟫| ^ p) ^ (1 / p) := fun g => by
    have h := aux_lrAcc_dual_bound q q' G H hH hrle (Y *ᵥ WithLp.ofLp g)
    -- `⟨aₖ, g⟩`, `⟨bᵢ, g⟩` are the entries of `Gᵀ z`, `Hᵀ z` at `z = Y g`
    have ha : ∀ k, ⟪a k, g⟫ = ((Y *ᵥ WithLp.ofLp g) ᵥ* G) k := fun k => by
      simp only [a, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct, vecMul, mulVec, Matrix.mul_apply, transpose_apply, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hb : ∀ i, ⟪b i, g⟫ = ((Y *ᵥ WithLp.ofLp g) ᵥ* H) i := fun i => by
      simp only [b, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct, vecMul, mulVec, Matrix.mul_apply, transpose_apply, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [ha, hb]
    rw [PiLp.norm_eq_sum (by simpa using hp0)] at h
    simpa [Real.norm_eq_abs, p] using h
  have hround := gaussian_rounding_le a b hp hr0 hpt
  -- `LR ≤ tr(Gᵀ Y) ≤ Σₖ ‖aₖ‖`
  have htr : trace (Gᵀ * Y) ≤ ∑ k, ‖a k‖ := Finset.sum_le_sum fun k _ =>
    (le_abs_self _).trans (by
      simpa [a, Real.norm_eq_abs] using PiLp.norm_apply_le (a k) k)
  -- `(Σᵢ ‖bᵢ‖^p)^{1/p} ≤ √m`
  have hbn : (∑ i, ‖b i‖ ^ p) ^ (1 / p) ≤ Real.sqrt m := by
    set M : Fin l → ℝ := fun i => ⨆ j, |(Hᵀ * Y) i j|
    have hM0 : ∀ i, 0 ≤ M i := fun i => Real.iSup_nonneg fun j => abs_nonneg _
    have hYn : (∑ i, M i ^ p) ^ (1 / p) ≤ 1 := by
      have := hY
      rw [PiLp.norm_eq_sum (by simpa using hp0)] at this
      simpa [Real.norm_eq_abs, abs_of_nonneg (hM0 _), M, p] using this
    -- `‖bᵢ‖ ≤ √m Mᵢ`, and `‖M‖_p ≤ 1`
    calc (∑ i, ‖b i‖ ^ p) ^ (1 / p) ≤ (∑ i, (Real.sqrt m * M i) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
            (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _)
              (aux_lrAcc_norm_le_sqrt_mul _) hp0.le) (by positivity)
      _ = Real.sqrt m * (∑ i, M i ^ p) ^ (1 / p) := by
          simp_rw [Real.mul_rpow (Real.sqrt_nonneg _) (hM0 _)]
          rw [← Finset.mul_sum, Real.mul_rpow (by positivity)
            (Finset.sum_nonneg fun i _ => by have := hM0 i; positivity), one_div,
            Real.rpow_rpow_inv (Real.sqrt_nonneg _) hp0.ne']
      _ ≤ Real.sqrt m * 1 := mul_le_mul_of_nonneg_left hYn (Real.sqrt_nonneg _)
      _ = Real.sqrt m := mul_one _
  -- `γ₁ LR ≤ γ₁ Σ ‖aₖ‖ ≤ r γ_p (Σ ‖bᵢ‖^p)^{1/p} ≤ r γ_p √m`
  have hγ1 : 0 < gaussMomentRoot 1 := by
    unfold gaussMomentRoot
    norm_num
    positivity
  have hγp : 0 ≤ gaussMomentRoot p := by
    unfold gaussMomentRoot
    exact Real.rpow_nonneg (mul_nonneg (by positivity)
      (Real.Gamma_pos_of_pos (by linarith)).le) _
  have hmain : LR ≤ gaussMomentRoot p * Real.sqrt m / gaussMomentRoot 1 * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ1]
    calc LR * gaussMomentRoot 1 ≤ gaussMomentRoot 1 * ∑ k, ‖a k‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hLRY.trans htr) hγ1.le
      _ ≤ r * (gaussMomentRoot p * (∑ i, ‖b i‖ ^ p) ^ (1 / p)) := hround
      _ ≤ r * (gaussMomentRoot p * Real.sqrt m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbn hγp) hr0
      _ = gaussMomentRoot p * Real.sqrt m * r := mul_comm _ _
  refine ⟨hmain, fun hlt => ?_⟩
  -- `C < LR ≤ C r` forces `r > 1`, and the maximizer leaves `E_q(H)`
  set C := gaussMomentRoot p * Real.sqrt m / gaussMomentRoot 1
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hγp (Real.sqrt_nonneg _)) hγ1.le
  have h1 : 1 < r := by
    have : C * 1 < C * r := by rw [mul_one]; exact hlt.trans_le hmain
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
