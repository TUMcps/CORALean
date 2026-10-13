import CORALean.Global.CoeffNorm
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The linear relaxation is exact for a parallelotope circumbody

[1, Thm. 16 (parallelotope)], corrected: for `q = ∞` and `H ∈ ℝ^{n×n}` invertible, some
maximizer `Y` of the dual program (Eq. 33), `max tr(Gᵀ Y)` subject to `‖Hᵀ Y‖_{L⊤∞,1} ≤ 1`, has
columns equal up to sign (Eq. 34), and `LR_∞(G, H) = r(Z(G), Z(H))`. The paper says every
maximizer does, which fails (`parallelotope_lr_exact_counterexample`); its proof finds the
maximum at an extreme point, which is what is proved here. With `M = H⁻¹ G` the only feasible
`X`, `LR_∞` is the largest row sum `Σⱼ |M_{kj}|`; `r` is the maximum of `‖M α‖_∞` over the cube,
the same number at `α = sign(M_{k·})`; and `tr(Gᵀ Y) = tr(Mᵀ Hᵀ Y)`, which is at most that row sum
once `Σₖ maxⱼ |(HᵀY)_{kj}| ≤ 1`, with equality at `Y = H⁻ᵀ e_k sign(M_{k·})ᵀ`. Dimension `n ≥ 1`.

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

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `tr(Aᵀ B) = Σₖ Σⱼ A_{kj} B_{kj}`. -/
theorem aux_trace_transpose_mul (A B : Matrix (Fin n) (Fin m) ℝ) :
    trace (Aᵀ * B) = ∑ k, ∑ j, A k j * B k j := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

/-- The sign of a real, as `±1`. -/
noncomputable def aux_sgnPM (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem aux_sgn_mul (x : ℝ) : x * aux_sgnPM x = |x| := by
  unfold aux_sgnPM
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]

theorem aux_abs_sgn (x : ℝ) : |aux_sgnPM x| = 1 := by
  unfold aux_sgnPM; split_ifs <;> simp

/-- `Σⱼ Z_{kj} M_{kj} ≤ (Σⱼ |M_{kj}|) maxⱼ |Z_{kj}|`, row by row. -/
theorem aux_row_le (M Z : Matrix (Fin n) (Fin m) ℝ) (k : Fin n) :
    ∑ j, M k j * Z k j ≤ (∑ j, |M k j|) * ⨆ j, |Z k j| := by -- --- PROOF ---
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc M k j * Z k j ≤ |M k j| * |Z k j| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |M k j| * ⨆ j, |Z k j| := mul_le_mul_of_nonneg_left
        (le_ciSup (f := fun j => |Z k j|) (Set.finite_range _).bddAbove j) (abs_nonneg _)

/-- At an invertible `H`, the norm of `G α` is `‖H⁻¹ G α‖_∞`: the preimage is unique. -/
theorem aux_coeffNorm_eq (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : IsUnit H.det) (α : Fin m → ℝ) :
    coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv ∞ ℝ (Fin n → ℝ)).toLinearMap)
      (G *ᵥ α) = ‖(H⁻¹ * G) *ᵥ α‖ := by -- --- PROOF ---
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv ∞ ℝ (Fin n → ℝ)).toLinearMap
  have happ : ∀ β, Hl β = H *ᵥ WithLp.ofLp β := fun β => rfl
  have hβ₀ : Hl (WithLp.toLp ∞ ((H⁻¹ * G) *ᵥ α)) = G *ᵥ α := by
    rw [happ, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]
  obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq Hl ⟨_, hβ₀⟩
  -- the minimizer is the unique preimage
  have huniq : β = WithLp.toLp ∞ ((H⁻¹ * G) *ᵥ α) := by
    rw [happ] at hβ
    have := congrArg (fun v => H⁻¹ *ᵥ v) hβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH, Matrix.one_mulVec] at this
    rw [← this]
  rw [← hβn, huniq, PiLp.norm_toLp]

/-- On the cube, `‖M α‖_∞` is at most the largest row sum. -/
theorem aux_norm_mulVec_le_rowSum (M : Matrix (Fin n) (Fin m) ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hk : ∀ i, ∑ j, |M i j| ≤ R) (α : Fin m → ℝ) (hα : ‖α‖ ≤ 1) :
    ‖M *ᵥ α‖ ≤ R := by -- --- PROOF ---
  refine (pi_norm_le_iff_of_nonneg hR0).mpr fun i => ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)).trans (hk i)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm α j)).trans hα)


-- =======================================  MAIN THEOREM  ======================================= --

theorem parallelotope_lr_exact [NeZero n] (G : Matrix (Fin n) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : IsUnit H.det) :
    (∃ Y : Matrix (Fin n) (Fin m) ℝ, ∑ k, (⨆ j, |(Hᵀ * Y) k j|) ≤ 1 ∧
        (∀ Y' : Matrix (Fin n) (Fin m) ℝ, ∑ k, (⨆ j, |(Hᵀ * Y') k j|) ≤ 1 →
          trace (Gᵀ * Y') ≤ trace (Gᵀ * Y)) ∧
        ∀ j j', (fun k => Y k j) = (fun k => Y k j') ∨ (fun k => Y k j) = -(fun k => Y k j')) ∧
      ∃ LR, IsLeast {N | ∃ X : Matrix (Fin n) (Fin m) ℝ, H * X = G ∧ N = ⨆ i, ∑ j, |X i j|} LR ∧
        IsGreatest ((fun α => coeffNorm ((Matrix.mulVecLin H) ∘ₗ
          (WithLp.linearEquiv ∞ ℝ (Fin n → ℝ)).toLinearMap) (G *ᵥ α)) ''
          Metric.closedBall 0 1) LR := by -- --- PROOF ---
  set M := H⁻¹ * G with hM
  have hHM : H * M = G := by
    rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]
  -- the row `k` of largest absolute sum
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => ∑ j, |M i j|)
    Finset.univ_nonempty
  set R := ∑ j, |M k j| with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsup : ∀ X : Matrix (Fin n) (Fin m) ℝ, X = M → (⨆ i, ∑ j, |X i j|) = R := by
    intro X hX
    rw [hX]
    exact le_antisymm (ciSup_le fun i => hk i (Finset.mem_univ i))
      (le_ciSup (f := fun i => ∑ j, |M i j|) (Set.finite_range _).bddAbove k)
  set σ : Fin m → ℝ := fun j => aux_sgnPM (M k j)
  refine ⟨⟨(H⁻¹)ᵀ * Matrix.of (fun i j => if i = k then σ j else 0), ?_, ?_, ?_⟩, R, ⟨?_, ?_⟩,
    ?_, ?_⟩
  · -- feasible: `Hᵀ Y = e_k σᵀ`
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hH,
      Matrix.transpose_one, Matrix.one_mul]
    rw [Finset.sum_eq_single k]
    · refine Real.iSup_le (fun j => ?_) zero_le_one
      simp [σ, aux_abs_sgn]
    · intro i _ hi
      simp [hi]
    · simp
  · -- its value is `R`, and no feasible `Y'` does better
    intro Y' hY'
    have hval : trace (Gᵀ * ((H⁻¹)ᵀ * Matrix.of (fun i j => if i = k then σ j else 0))) = R := by
      rw [← hHM, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ,
        ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hH, Matrix.transpose_one, Matrix.one_mul,
        aux_trace_transpose_mul, Finset.sum_eq_single k]
      · simp only [Matrix.of_apply, σ, if_true, aux_sgn_mul]
        exact hR.symm
      · intro i _ hi; simp [hi]
      · simp
    rw [hval, ← hHM, Matrix.transpose_mul, Matrix.mul_assoc, aux_trace_transpose_mul]
    calc ∑ i, ∑ j, M i j * (Hᵀ * Y') i j ≤ ∑ i, R * ⨆ j, |(Hᵀ * Y') i j| :=
          Finset.sum_le_sum fun i _ => (aux_row_le M (Hᵀ * Y') i).trans
            (mul_le_mul_of_nonneg_right (hk i (Finset.mem_univ i))
              (Real.iSup_nonneg fun _ => abs_nonneg _))
      _ = R * ∑ i, ⨆ j, |(Hᵀ * Y') i j| := by rw [Finset.mul_sum]
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left hY' hR0
      _ = R := mul_one R
  · -- the columns are `σⱼ H⁻ᵀ e_k`, equal up to sign
    intro j j'
    have hcol : ∀ j, (fun i => ((H⁻¹)ᵀ * Matrix.of (fun i j => if i = k then σ j else 0)) i j) =
        σ j • fun i => (H⁻¹)ᵀ i k := fun j => by
      funext i
      simp [Matrix.mul_apply, Finset.sum_ite_eq', mul_comm]
    rw [hcol j, hcol j']
    unfold σ aux_sgnPM
    split_ifs <;> simp
  · exact ⟨M, hHM, (hsup M rfl).symm⟩
  · rintro _ ⟨X, hX, rfl⟩
    have : X = M := by
      rw [hM, ← hX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hH, Matrix.one_mul]
    exact (hsup X this).ge
  · -- `r` at `α = σ`: the point `G σ` has the unique preimage `M σ`
    refine ⟨σ, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
        rw [Real.norm_eq_abs]; exact (aux_abs_sgn _).le
    · show coeffNorm _ (G *ᵥ σ) = R
      rw [aux_coeffNorm_eq G H hH σ, ← hM]
      refine le_antisymm (aux_norm_mulVec_le_rowSum M hR0 (fun i => hk i (Finset.mem_univ i)) σ
        ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
          rw [Real.norm_eq_abs]; exact (aux_abs_sgn _).le)) ?_
      have h := norm_le_pi_norm (M *ᵥ σ) k
      rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct] at h
      simp only [σ, aux_sgn_mul] at h
      rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
      exact h
  · rintro _ ⟨α, hα, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hα
    show coeffNorm _ (G *ᵥ α) ≤ R
    rw [aux_coeffNorm_eq G H hH α, ← hM]
    exact aux_norm_mulVec_le_rowSum M hR0 (fun i => hk i (Finset.mem_univ i)) α hα

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
