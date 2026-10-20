module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.LinearRelaxationDual
public import CORALean.Global.MatrixFunctionalEqSumSingle
public import CORALean.Global.MatrixFunctionalMulEqSum
public import CORALean.Global.Basic
public import CORALean.Global.PiLpNormToLpLeOfAbsLe
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# The linear relaxation is exact when the dual maximizer has equal columns

[1, Thm. 16]: for `G ∈ ℝ^{n×m}`, `H ∈ ℝ^{n×l}` and `Y` a maximizer of the dual program (Eq. 33),
`max tr(Gᵀ Y)` subject to `‖Hᵀ Y‖_{L⊤∞,q*} ≤ 1`, whose columns are equal up to sign (Eq. 34),
`LR_q(G, H) = r(Z(G), E_q(H))`: the minimum of Eq. 29 and the maximum of Eq. 15 exist and agree.
`H` need not be surjective: a maximizer forces `G`'s columns into the range of `H`, since otherwise
a `Z` with `Hᵀ Z = 0` and `tr(Gᵀ Z) ≠ 0` makes the program unbounded. By `lr_exists_dual`
`LR_q ≤ tr(Gᵀ Y)` at the maximizer, and with `Y = y σᵀ`, `tr(Gᵀ Y) ≤ ‖β‖_q` by Hölder for the
minimal `β` with `H β = G σ`, so `LR_q ≤` the norm of `G σ` `≤ r ≤ LR_q`.

## Inputs
* `q` – exponent of the coefficient norm
* `q'` – its conjugate exponent
* `G` – zonotope generator matrix
* `H` – ellipsotope generator matrix
* `Y` – dual maximizer

## Hypotheses
* `hY` – the maximizer is feasible
* `hYmax` – the maximizer attains the dual maximum
* `hcol` – the maximizer's columns are equal up to sign

## Conclusion
* the relaxation value and the containment radius both exist and agree

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

open scoped ENNReal NNReal
open Matrix

variable {n m l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Hölder: `Σ aᵢ bᵢ ≤ ‖a‖_{q'} ‖b‖_q`, endpoints included. -/
theorem aux_lrExact_holder (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (a b : Fin l → ℝ) : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_exact_of_columns_eq_up_to_sign (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ) (Y : Matrix (Fin n) (Fin m) ℝ)
    (hY : ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y) i j|)‖ ≤ 1)
    (hYmax : ∀ Y' : Matrix (Fin n) (Fin m) ℝ,
      ‖WithLp.toLp q' (fun i => ⨆ j, |(Hᵀ * Y') i j|)‖ ≤ 1 → trace (Gᵀ * Y') ≤ trace (Gᵀ * Y))
    (hcol : ∀ j j', (fun k => Y k j) = (fun k => Y k j') ∨
      (fun k => Y k j) = -(fun k => Y k j')) : -- --- CONCL ---
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
      rw [functional_mul_eq_sum f H] at h0
      simpa [single_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq] using h0
    have hfeas := hYmax (Y + (f G)⁻¹ • Z) (by
      rwa [Matrix.mul_add, Matrix.mul_smul, hHZ, smul_zero, add_zero])
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul,
      trace_transpose_mul_eq_sum G Z] at hfeas
    have hGZ : ∑ k, ∑ j, G k j * Z k j = f G := (functional_eq_sum_single f G).symm
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
    refine (coeffNorm_le Hl _).trans (PiLp.norm_toLp_le_of_abs_le q _ _ fun i => ?_)
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) ((norm_le_pi_norm α j).trans hα)
  -- `tr(Gᵀ Y) = (Hᵀ y)ᵀ β ≤ ‖β‖_q` for the minimal `β` with `H β = G σ`
  have hlow : trace (Gᵀ * Y) ≤ coeffNorm Hl (G *ᵥ σ) := by
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j₀⟩⟩
    · rw [trace_transpose_mul_eq_sum]
      simpa using coeffNorm_nonneg Hl (G *ᵥ σ)
    obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq Hl ⟨WithLp.toLp q (X₀ *ᵥ σ), by
      rw [hHl, WithLp.ofLp_toLp, mulVec_mulVec, hX₀]⟩
    have htr : trace (Gᵀ * Y) = ∑ i, (y ᵥ* H) i * WithLp.ofLp β i := by
      calc trace (Gᵀ * Y) = y ⬝ᵥ (G *ᵥ σ) := by
            rw [trace_transpose_mul_eq_sum]
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
      refine (PiLp.norm_toLp_le_of_abs_le q' _ _ fun i => ?_).trans hY
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
