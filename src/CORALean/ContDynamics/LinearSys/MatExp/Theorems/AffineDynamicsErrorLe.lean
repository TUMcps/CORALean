module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.AffineDynamicsErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineDynamicsError
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.GenMinus
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsConstCorrectionMatrixLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrectionMatrixLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Global.Err
public import CORALean.Global.EuclideanGenOpNorm

@[expose] public section

/-!
# `affineDynamicsError` is under its own explicit bound

[1, Lemma 3]'s asymptotics reduce to `affineDynamicsErrorBound`'s, a real-valued computation.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An interval matrix whose two endpoints are both under `ρ` has centre and radius under `ρ`
too, which is the form `mtimesIntervalMat_subset_closedBall` asks for. -/
theorem MatExp.aux_center_radius_le {m : ℕ} {ρ : ℝ} {IM : Interval (Mat ℝ m m)}
    (h : ∀ j k, |IM.inf j k| ≤ ρ ∧ |IM.sup j k| ≤ ρ) :
    (∀ j k, |IM.center j k| ≤ ρ) ∧ ∀ j k, |IM.radius j k| ≤ ρ := by -- --- PROOF ---
  constructor
  · intro j k
    obtain ⟨hinf, hsup⟩ := h j k
    have hval : IM.center j k = (2:ℝ)⁻¹ * (IM.inf j k + IM.sup j k) := rfl
    have habs := abs_add_le (IM.inf j k) (IM.sup j k)
    rw [hval, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    linarith
  · intro j k
    obtain ⟨hinf, hsup⟩ := h j k
    have hval : IM.radius j k = (2:ℝ)⁻¹ * (IM.sup j k - IM.inf j k) := rfl
    have habs := abs_sub (IM.sup j k) (IM.inf j k)
    rw [hval, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    linarith

/-- Every point of the curvature enclosure is within `√n · (2ρ_F Σ_H + 2ρ_G Σ_ũ)` of the
origin: the two interval products are each bounded at the supremum norm, and `√n` carries that
to `‖·‖₂`. -/
theorem MatExp.aux_norm₂_le_of_mem_curvatureEnclosure (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) {ρF ρG : ℝ} (hρF : 0 ≤ ρF) (hρG : 0 ≤ ρG)
    (hF : ∀ j k, |(MatExp.correctionMatrix A Δt η).inf j k| ≤ ρF
      ∧ |(MatExp.correctionMatrix A Δt η).sup j k| ≤ ρF)
    (hG : ∀ j k, |(MatExp.constCorrectionMatrix A Δt η).inf j k| ≤ ρG
      ∧ |(MatExp.constCorrectionMatrix A Δt η).sup j k| ≤ ρG) :
    ∀ y ∈ (MatExp.curvatureEnclosure A H ũ Δt η).construct,
      ‖y‖₂ ≤ Real.sqrt n * ((ρF + ρF) * ∑ j, H.absBound j
        + (ρG + ρG) * ∑ j, |ũ j|) := by -- --- PROOF ---
  obtain ⟨hFc, hFr⟩ := MatExp.aux_center_radius_le hF
  obtain ⟨hGc, hGr⟩ := MatExp.aux_center_radius_le hG
  have hpt : ∑ j, (Zonotope.ofPoint ũ).absBound j = ∑ j, |ũ j| := by
    simp [Zonotope.absBound, Zonotope.ofPoint]
  intro y hy
  rw [MatExp.curvatureEnclosure, ← Zonotope.plus_exact] at hy
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
  have h₁ := Zonotope.mtimesIntervalMat_subset_closedBall _ H hρF hρF hFc hFr hy₁
  have h₂ := Zonotope.mtimesIntervalMat_subset_closedBall _ (Zonotope.ofPoint ũ) hρG hρG hGc hGr hy₂
  rw [Metric.mem_closedBall, dist_zero_right] at h₁ h₂
  rw [hpt] at h₂
  -- the supremum-norm bounds on the two summands, carried to `‖·‖₂` by `√n`
  calc ‖y₁ + y₂‖₂ ≤ ‖y₁‖₂ + ‖y₂‖₂ := norm₂_add_le _ _
    _ ≤ Real.sqrt n * ‖y₁‖ + Real.sqrt n * ‖y₂‖ :=
        add_le_add (norm₂_le_sqrt_mul_norm _) (norm₂_le_sqrt_mul_norm _)
    _ ≤ Real.sqrt n * ((ρF + ρF) * ∑ j, H.absBound j) + Real.sqrt n * ((ρG + ρG) * ∑ j, |ũ j|) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg _))
    _ = Real.sqrt n * ((ρF + ρF) * ∑ j, H.absBound j + (ρG + ρG) * ∑ j, |ũ j|) := by ring

/-- `G^{(-)}_h`'s columns are each under `n‖e^{AΔt} - I‖` times their own generator's `ℓ¹`
reach, and `genOpNorm₂_le_sum_norm₂` is what turns that into a bound on the operator norm. -/
theorem MatExp.aux_genOpNorm₂_genMinus_le (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n)) (Δt : ℝ) :
    genOpNorm₂ (MatExp.genMinus A H Δt)
      ≤ (n : ℝ) * ‖exp (Δt • A) - 1‖ * ∑ l, ∑ j, |H.G l j| := by -- --- PROOF ---
  refine (genOpNorm₂_le_sum_norm₂ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  -- one column, read off the rows of `e^{AΔt} - I` it comes from
  calc ‖MatExp.genMinus A H Δt l‖₂
      ≤ ∑ i, |MatExp.genMinus A H Δt l i| := norm₂_le_sum_abs _
    _ ≤ ∑ _i : Fin n, ‖exp (Δt • A) - 1‖ * ∑ j, |H.G l j| := Finset.sum_le_sum fun i _ => by
        calc |MatExp.genMinus A H Δt l i|
            = |∑ j, (exp (Δt • A) - 1) i j * H.G l j| := rfl
          _ ≤ ∑ j, |(exp (Δt • A) - 1) i j * H.G l j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, ‖exp (Δt • A) - 1‖ * |H.G l j| := Finset.sum_le_sum fun j _ => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (abs_entry_le_norm _ i j) (abs_nonneg _)
          _ = ‖exp (Δt • A) - 1‖ * ∑ j, |H.G l j| := (Finset.mul_sum _ _ _).symm
    _ = (n : ℝ) * ‖exp (Δt • A) - 1‖ * ∑ j, |H.G l j| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `affineDynamicsError` is under its own explicit `Δt`-polynomial bound. -/
theorem MatExp.affineDynamicsError_le (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n)
    {Δt : ℝ} (hΔt : 0 ≤ Δt) {η : ℕ} (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1) :
    MatExp.affineDynamicsError A H ũ Δt η
      ≤ MatExp.affineDynamicsErrorBound A H ũ Δt η := by -- --- PROOF ---
  have hc : (0:ℝ) ≤ Δt * ‖A‖ := mul_nonneg hΔt (norm_nonneg _)
  have hb0 : (0:ℝ) ≤ MatExp.expRemainderBound (Δt • A) η := by
    rw [MatExp.expRemainderBound]
    have h1 : (0:ℝ) < 1 - ‖Δt • A‖ / ((η : ℝ) + 2) := by linarith
    positivity
  have hexp1 : (0:ℝ) ≤ Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ :=
    by linarith [Real.add_one_le_exp (Δt * ‖A‖)]
  set ρF := Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ + MatExp.expRemainderBound (Δt • A) η with hρFdef
  set ρG := Δt * (Real.exp (Δt * ‖A‖) - 1) + Δt * MatExp.expRemainderBound (Δt • A) η with hρGdef
  have hρF : (0:ℝ) ≤ ρF := by rw [hρFdef]; linarith
  have hρG : (0:ℝ) ≤ ρG := by
    rw [hρGdef]
    have := Real.add_one_le_exp (Δt * ‖A‖)
    have h1 : (0:ℝ) ≤ Real.exp (Δt * ‖A‖) - 1 := by linarith
    positivity
  have hSumH : (0:ℝ) ≤ ∑ j, H.absBound j := Finset.sum_nonneg fun j _ => by
    rw [Zonotope.absBound]; positivity
  have hSumU : (0:ℝ) ≤ ∑ j, |ũ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- the curvature enclosure, at `err`
  have herr : 2 * err (MatExp.curvatureEnclosure A H ũ Δt η).construct
      ≤ 4 * (n : ℝ) * (ρF * ∑ j, H.absBound j + ρG * ∑ j, |ũ j|) := by
    have hr : (0:ℝ) ≤ Real.sqrt n * ((ρF + ρF) * ∑ j, H.absBound j + (ρG + ρG) * ∑ j, |ũ j|) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg (mul_nonneg (by linarith) hSumH) (mul_nonneg (by linarith) hSumU))
    have hbound := err_le_of_forall_norm₂_le hr
      (MatExp.aux_norm₂_le_of_mem_curvatureEnclosure A H ũ Δt η hρF hρG
        (fun j k => MatExp.abs_correctionMatrix_le A hΔt hε j k)
        (fun j k => MatExp.abs_constCorrectionMatrix_le A hΔt hε j k))
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hkey : Real.sqrt n * (Real.sqrt n * ((ρF + ρF) * ∑ j, H.absBound j
        + (ρG + ρG) * ∑ j, |ũ j|))
        = 2 * (n : ℝ) * (ρF * ∑ j, H.absBound j + ρG * ∑ j, |ũ j|) := by
      rw [← mul_assoc, hsq]; ring
    rw [hkey] at hbound
    linarith
  -- and the generators the step moves, at the operator norm
  have hgen : Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt)
      ≤ Real.sqrt H.h * ((n : ℝ) * (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * ∑ l, ∑ j, |H.G l j|) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine (MatExp.aux_genOpNorm₂_genMinus_le A H Δt).trans ?_
    have hG : (0:ℝ) ≤ ∑ l, ∑ j, |H.G l j| :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have hE := norm_exp_smul_sub_one_le A hΔt
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hn) hG
  rw [MatExp.affineDynamicsError, MatExp.affineDynamicsErrorBound]
  exact add_le_add herr hgen

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
