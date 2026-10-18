module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemIntervalCorrectionMatrixOfRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSubPeanoBakerSumLe

@[expose] public section

/-!
# A run inside a box, between the two ends of a step, is CORA's interpolation

`expDiff_mem_intervalCorrectionMatrix` for a matrix that varies in time. A
solution of `x(s) = x(0) + ∫₀ˢ A(σ) x(σ) dσ` on `[0, r]`, every `A(σ)` in `B`, is
at every `t ∈ [0, r]` the straight line `(1 - λ) x(0) + λ Φ x(0)` from its start
to a member `Φ` of the step's exponential enclosure, plus `F x(0)` for a member `F`
of the correction matrix, `λ = t / r` — the very two interval matrices
`'constParam'` uses, which is what CORA's `initReach` computes for `'varParam'`.

`MatExp.norm_sub_peanoBakerSum_le` bounds what the first `η + 1` Peano–Baker terms
miss at `t`, and `MatExp.exists_mem_intervalCorrectionMatrix_of_remainder` is the
rest: the terms are the interpolation, the miss is the correction's widening.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of the integral equation at a matrix that stays in `B` is, at every
time of the step, the interpolation from its start to a member of the step's
exponential enclosure, plus a member of the correction matrix applied to its start. -/
theorem MatExp.exists_mem_intervalCorrectionMatrix_of_integral {B : Interval (Mat ℝ n n)}
    {A : ℝ → Mat ℝ n n} (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {x : ℝ → Vec ℝ n} {r : ℝ} (hr : 0 < r)
    (hxc : ContinuousOn x (Set.Icc 0 r))
    (hx : ∀ s ∈ Set.Icc 0 r, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) {m : ℕ}
    (hε : ‖(Interval.smul r B).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- STMT ---
    ∃ Φ ∈ (MatExp.expIntervalEnclosure (Interval.smul r B) (m + 2)).construct,
      ∃ F ∈ (MatExp.intervalCorrectionMatrix B r (m + 2)).construct,
        x t = ((1 - t / r) • x 0 + (t / r) • (Φ *ᵥ x 0)) + F *ᵥ x 0 := by -- --- PROOF ---
  have habs : ‖(Interval.smul t B).absMax‖ ≤ ‖(Interval.smul r B).absMax‖ := by
    rw [Interval.absMax_smul B ht0, Interval.absMax_smul B hr.le, norm_smul, norm_smul,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hεt : ‖(Interval.smul t B).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hε
  -- what the terms miss at `t` is short, and the rest is the expansion's
  have hρ := MatExp.norm_sub_peanoBakerSum_le hA hAB ht0
    (hxc.mono (Set.Icc_subset_Icc le_rfl htr)) (fun s hs => hx s ⟨hs.1, hs.2.trans htr⟩)
    (m + 2) hεt
  obtain ⟨Φ, hΦ, F, hF, heq⟩ :=
    MatExp.exists_mem_intervalCorrectionMatrix_of_remainder hA hAB hr hε ht0 htr (x 0) _ hρ
  refine ⟨Φ, hΦ, F, hF, ?_⟩
  rw [← heq]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
