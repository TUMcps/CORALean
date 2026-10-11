import CORALean.Global.CoeffNorm
import CORALean.Global.LinearRelaxationDual
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The linear relaxation is exact when the dual maximizer has equal columns

[1, Thm. 16]: for `G ∈ ℝ^{n×m}`, `H ∈ ℝ^{n×l}` and `Y` a maximizer of the dual program (Eq. 33),
`max tr(Gᵀ Y)` subject to `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1`, whose columns are equal up to sign (Eq. 34),
`LR_q(G, H) = r(Z(G), E_q(H))`: the minimum of Eq. 29 and the maximum of Eq. 15 exist and agree.
`H` need not be surjective: a maximizer forces `G`'s columns into the range of `H`, since
otherwise a `Z` with `Hᵀ Z = 0` and `tr(Gᵀ Z) ≠ 0` makes the program unbounded.
Strong duality of Eq. 32 is `lr_exists_dual`: the minimum `LR_q` is attained and some feasible
`Y*` has `tr(Gᵀ Y*) ≥ LR_q`, so `LR_q ≤ tr(Gᵀ Y)` at the maximizer.
With `Y = y σᵀ`, `tr(Gᵀ Y) = yᵀ G σ = (Hᵀ y)ᵀ β ≤ ‖β‖_q` for the minimal `β` with `H β = G σ`,
by Hölder, so `LR_q ≤` the norm of `G σ` `≤ r ≤ LR_q`. `q* = q'` is the Hölder conjugate.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal NNReal
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `q`-norm is monotone in the absolute values of the entries. -/
theorem aux_lrExact_norm_mono (q : ℝ≥0∞) [Fact (1 ≤ q)] (a b : Fin l → ℝ)
    (h : ∀ i, |a i| ≤ b i) : ‖WithLp.toLp q a‖ ≤ ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  have hb : ∀ i, 0 ≤ b i := fun i => (abs_nonneg _).trans (h i)
  by_cases hq : q = ∞
  · subst hq
    simp only [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (h i).trans ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm b i))
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    simp only [Real.norm_eq_abs]
    exact Real.rpow_le_rpow (abs_nonneg _) ((h i).trans (le_abs_self _)) hq0.le

/-- Hölder: `Σ aᵢ bᵢ ≤ ‖a‖_{q'} ‖b‖_q`, endpoints included. -/
theorem aux_lrExact_holder (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q'] (a b : Fin l → ℝ) :
    ∑ i, a i * b i ≤ ‖WithLp.toLp q' a‖ * ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  by_cases hq : q = ∞
  · -- `q' = 1`
    have hq' : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q q').mp hq
    subst hq hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |a i| * ‖b‖ := mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i) (abs_nonneg _)
  by_cases hq1 : q = 1
  · -- `q' = ∞`
    have hq' : q' = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q' q).mpr hq1
    subst hq1 hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ ‖a‖ * |b i| := mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i) (abs_nonneg _)
  · -- `1 < q < ∞`: the real Hölder inequality
    have hq'1 : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1
    have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq'0 : 0 < q'.toReal :=
      ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'1
    have hR : q'.toReal.HolderConjugate q.toReal := by
      simpa using ENNReal.HolderTriple.toReal 1 hq'0 hq0
    rw [PiLp.norm_eq_sum hq'0, PiLp.norm_eq_sum hq0]
    simpa [Real.norm_eq_abs] using Real.inner_le_Lp_mul_Lq Finset.univ a b hR

/-- `tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`. -/
theorem aux_lrExact_trace {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) :
    trace (Aᵀ * B) = ∑ k, ∑ j, A k j * B k j := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

/-- A functional on matrices is `M ↦ Σ M_{kj} f(E_{kj})`. -/
theorem aux_lrExact_functional_eq (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) :
    f M = ∑ k, ∑ j, M k j * f (single k j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single k j (M k j) = M k j • single k j (1 : ℝ) by simp, map_smul, smul_eq_mul]

/-- After `X ↦ H X`, it is `X ↦ Σ (Hᵀ Z)_{ij} X_{ij}` with `Z_{kj} = f(E_{kj})`. -/
theorem aux_lrExact_functional_mul (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (X : Matrix (Fin l) (Fin m) ℝ) :
    f (H * X) = ∑ i, ∑ j,
      (Hᵀ * Matrix.of fun k j => f (single k j (1 : ℝ))) i j * X i j := by -- --- PROOF ---
  -- both sides are `tr((H X)ᵀ Z) = tr(Xᵀ (Hᵀ Z))`
  rw [aux_lrExact_functional_eq f]
  have h := aux_lrExact_trace (H * X) (Matrix.of fun k j => f (single k j (1 : ℝ)))
  rw [transpose_mul, Matrix.mul_assoc, aux_lrExact_trace] at h
  simp only [of_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_exact_of_columns_eq_up_to_sign (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ) (Y : Matrix (Fin n) (Fin m) ℝ)
    (hY : ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y) i j|)‖ ≤ 1)
    (hYmax : ∀ Y' : Matrix (Fin n) (Fin m) ℝ,
      ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y') i j|)‖ ≤ 1 → trace (Gᵀ * Y') ≤ trace (Gᵀ * Y))
    (hcol : ∀ j j', (fun k => Y k j) = (fun k => Y k j') ∨
      (fun k => Y k j) = -(fun k => Y k j')) :
    ∃ LR, IsLeast {N | ∃ X : Matrix (Fin l) (Fin m) ℝ, H * X = G ∧
        N = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖} LR ∧
      IsGreatest ((fun α => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
        (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) (G *ᵥ α)) ''
        Metric.closedBall 0 1) LR := by -- --- PROOF ---
  haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
  set L := mulLeftLinearMap (Fin m) ℝ H with hL
  -- a maximizer puts `G` in the range of `X ↦ H X`: else `Y + t Z` is unbounded
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, H * X₀ = G := by
    by_contra hne
    have hG : G ∉ LinearMap.range L := fun ⟨X, hX⟩ => hne ⟨X, hX⟩
    obtain ⟨f, hfG, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hG inferInstance
    set Z : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun k j => f (single k j 1)
    have hHZ : Hᵀ * Z = 0 := by
      ext i j
      have h0 : f (H * single i j (1 : ℝ)) = 0 := by
        have : f (L (single i j 1)) ∈ (LinearMap.range L).map f := ⟨_, ⟨_, rfl⟩, rfl⟩
        rw [hf] at this
        simpa [L] using (Submodule.mem_bot ℝ).mp this
      rw [aux_lrExact_functional_mul f H] at h0
      simpa [single_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq] using h0
    have hfeas := hYmax (Y + (f G)⁻¹ • Z) (by
      rwa [Matrix.mul_add, Matrix.mul_smul, hHZ, smul_zero, add_zero])
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, aux_lrExact_trace G Z] at hfeas
    have hGZ : ∑ k, ∑ j, G k j * Z k j = f G := (aux_lrExact_functional_eq f G).symm
    rw [hGZ, smul_eq_mul, inv_mul_cancel₀ hfG] at hfeas
    linarith
  -- strong duality of Eq. 32: the minimum `d` of Eq. 29, and a dual certificate attaining it
  obtain ⟨d, hdL, Ys, hYs, hdYs⟩ := lr_exists_dual q q' G H ⟨X₀, hX₀⟩
  obtain ⟨Xs, hXs, hXsd⟩ := hdL.1
  have hdY : d ≤ trace (Gᵀ * Y) := hdYs.trans (hYmax Ys hYs)
  -- `Y = y σᵀ`
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, ∀ j, (fun k => Y k j) = y ∨ (fun k => Y k j) = -y := by
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j₀⟩⟩
    · exact ⟨0, fun j => isEmptyElim j⟩
    · exact ⟨fun k => Y k j₀, fun j => hcol j j₀⟩
  set σ : Fin m → ℝ := fun j => if (fun k => Y k j) = y then 1 else -1
  have hYσ : ∀ k j, Y k j = σ j * y k := fun k j => by
    by_cases h : (fun k => Y k j) = y
    · simp only [σ, h, if_true, one_mul]
      exact congrFun h k
    · have := congrFun ((hy j).resolve_left h) k
      simp only [σ, h, if_false, neg_one_mul]
      simpa using this
  -- `σ` is a sign vector, a corner of the cube
  have hσ1 : ∀ j, |σ j| = 1 := fun j => by
    simp only [σ]
    split_ifs <;> simp
  have hσ : σ ∈ Metric.closedBall (0 : Fin m → ℝ) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by rw [Real.norm_eq_abs, hσ1]
  -- every `G α` on the cube has the preimage `Xs α`
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  have hHl : ∀ β, Hl β = H *ᵥ WithLp.ofLp β := fun β => rfl
  have hup : ∀ α ∈ Metric.closedBall (0 : Fin m → ℝ) 1, coeffNorm Hl (G *ᵥ α) ≤ d :=
    fun α hα => by
    rw [mem_closedBall_zero_iff] at hα
    have hGα : G *ᵥ α = Hl (WithLp.toLp q (Xs *ᵥ α)) := by
      rw [hHl, WithLp.ofLp_toLp, mulVec_mulVec, hXs]
    rw [hGα, hXsd]
    refine (coeffNorm_le Hl _).trans (aux_lrExact_norm_mono q _ _ fun i => ?_)
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) ((norm_le_pi_norm α j).trans hα)
  -- `tr(Gᵀ Y) = (Hᵀ y)ᵀ β ≤ ‖β‖_q` for the minimal `β` with `H β = G σ`
  have hlow : trace (Gᵀ * Y) ≤ coeffNorm Hl (G *ᵥ σ) := by
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j₀⟩⟩
    · rw [aux_lrExact_trace]
      simpa using coeffNorm_nonneg Hl (G *ᵥ σ)
    obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq Hl ⟨WithLp.toLp q (X₀ *ᵥ σ), by
      rw [hHl, WithLp.ofLp_toLp, mulVec_mulVec, hX₀]⟩
    have htr : trace (Gᵀ * Y) = ∑ i, (y ᵥ* H) i * WithLp.ofLp β i := by
      calc trace (Gᵀ * Y) = y ⬝ᵥ (G *ᵥ σ) := by
            rw [aux_lrExact_trace]
            simp only [hYσ, dotProduct, mulVec, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = y ⬝ᵥ (H *ᵥ WithLp.ofLp β) := by rw [← hHl, hβ]
        _ = (y ᵥ* H) ⬝ᵥ WithLp.ofLp β := dotProduct_mulVec _ _ _
        _ = _ := rfl
    have hrow : ∀ i j, (Hᵀ * Y) i j = σ j * (y ᵥ* H) i := fun i j => by
      simp only [mul_apply, transpose_apply, hYσ, vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    -- Eq. 36: the rows of `Hᵀ Y` are `σᵀ` times `(Hᵀ y)ᵢ`, so `‖Hᵀ y‖_{q'} ≤ 1`
    have h1 : ‖WithLp.toLp q' (y ᵥ* H)‖ ≤ 1 := by
      refine (aux_lrExact_norm_mono q' _ _ fun i => ?_).trans hY
      refine le_trans ?_ (le_ciSup (f := fun j => |(Hᵀ * Y) i j|) (Set.finite_range _).bddAbove j₀)
      rw [hrow, abs_mul, hσ1, one_mul]
    rw [htr, ← hβn]
    refine (aux_lrExact_holder q q' _ _).trans ?_
    calc _ ≤ 1 * ‖WithLp.toLp q (WithLp.ofLp β)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖β‖ := by simp
  -- `LR_q = d ≤ tr(Gᵀ Y) ≤ ‖G σ‖ ≤ r ≤ LR_q`
  have hσd : coeffNorm Hl (G *ᵥ σ) = d := le_antisymm (hup σ hσ) (hdY.trans hlow)
  refine ⟨d, hdL, ⟨⟨σ, hσ, hσd⟩, ?_⟩⟩
  rintro _ ⟨α, hα, rfl⟩
  exact hup α hα

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
