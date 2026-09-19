import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsConstCorrectionMatrixLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrectionMatrixLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.Global.Err
import CORALean.Global.EuclideanGenOpNorm

/-!
# `Δε^h_k`, eq. (23)

`Δε^h_k(Δt,η) := 2·err(C) + √γ_h ‖G^{(-)}_h‖₂`, the error [1, Prop. 1] charges the affine
dynamics for one step. `C` is Line 8 of [1, Alg. 1] — `F(Δt,η)H(t_k) ⊕ G(Δt,η)ũ`, whose two
interval matrices (eq. 15-16) are already this tree's `correctionMatrix` and
`constCorrectionMatrix`, the asymmetric interval `I_i(Δt)` of eq. (17) being what
`min (corrTerm …) 0`/`max (corrTerm …) 0` already spell — and `G^{(-)}_h = (e^{AΔt}-I)G_h`.

`affineDynamicsErrorBound` is an explicit `Δt`-polynomial dominating it, so [1, Lemma 3]'s
asymptotics reduce to that bound's, a real-valued computation. `Zonotope.mtimesIntervalMat` is
CORA's own `mtimes` at an interval matrix, so `C` is the set Line 8 computes rather than the
exact product it encloses, which is what `err(C)` is about.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


/-- Line 8 of [1, Alg. 1]: the curvature enclosure `C = F(Δt,η)H(t_k) ⊕ G(Δt,η)ũ`. -/
noncomputable def MatExp.curvatureEnclosure (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  (Zonotope.mtimesIntervalMat (MatExp.correctionMatrix A Δt η) H).plus
    (Zonotope.mtimesIntervalMat (MatExp.constCorrectionMatrix A Δt η) (Zonotope.ofPoint ũ))

/-- [1]'s eq. (23) `G^{(-)}_h = (e^{AΔt} - I_n)G_h`, one column per generator. -/
noncomputable def MatExp.genMinus (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n)) (Δt : ℝ) :
    Fin H.h → Vec ℝ n :=
  fun l => (exp (Δt • A) - 1).mulVec (H.G l)

/-- [1]'s eq. (23): `Δε^h_k(Δt,η) := 2·err(C) + √γ_h ‖G^{(-)}_h‖₂`. -/
noncomputable def MatExp.affineDynamicsError (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  2 * err (MatExp.curvatureEnclosure A H ũ Δt η).construct
    + Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt)

/-- The `Δt`-polynomial dominating `affineDynamicsError`. -/
noncomputable def MatExp.affineDynamicsErrorBound (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  4 * (n : ℝ) * ((Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ + MatExp.expRemainderBound (Δt • A) η)
        * (∑ j, H.absBound j)
      + (Δt * (Real.exp (Δt * ‖A‖) - 1) + Δt * MatExp.expRemainderBound (Δt • A) η)
        * (∑ j, |ũ j|))
    + Real.sqrt H.h * ((n : ℝ) * (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * ∑ l, ∑ j, |H.G l j|)


theorem MatExp.affineDynamicsError_nonneg (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : 0 ≤ MatExp.affineDynamicsError A H ũ Δt η :=
  add_nonneg (mul_nonneg (by norm_num) (err_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (genOpNorm₂_nonneg _))


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


/-- Eventually, as `Δt → 0⁺`, `affineDynamicsError` is under one linear bound `K · Δt`: once
`Δt ≤ 1` and `Δt‖A‖ ≤ 1`, every `Δt`-dependent factor of `affineDynamicsErrorBound` is under
`Δt` times a `Δt`-free constant. -/
theorem MatExp.exists_affineDynamicsError_le_const_mul (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (η : ℕ) :
    ∃ K : ℝ, ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ),
      MatExp.affineDynamicsError A H ũ Δt η ≤ K * Δt := by -- --- PROOF ---
  -- the three `Δt`-free constants the bound's three `Δt`-dependent factors are traded for
  set CE := 2 * (‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) with hCEdef
  set cF := ‖A‖ ^ 2 * Real.exp 1 + CE with hcFdef
  set cG := Real.exp 1 - 1 + CE with hcGdef
  have hCE0 : (0:ℝ) ≤ CE := by rw [hCEdef]; positivity
  have hSumH : (0:ℝ) ≤ ∑ j, H.absBound j := Finset.sum_nonneg fun j _ => by
    rw [Zonotope.absBound]; positivity
  have hSumU : (0:ℝ) ≤ ∑ j, |ũ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSumG : (0:ℝ) ≤ ∑ l, ∑ j, |H.G l j| :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨4 * (n:ℝ) * (cF * ∑ j, H.absBound j + cG * ∑ j, |ũ j|)
    + Real.sqrt H.h * ((n:ℝ) * (‖A‖ * Real.exp 1) * ∑ l, ∑ j, |H.G l j|), ?_⟩
  -- the two conditions everything below runs under, each holding eventually
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hev1 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt ≤ 1 := hid.eventually_le_const (by norm_num)
  have hev2 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt * ‖A‖ ≤ 1 := by
    have h : Tendsto (fun Δt : ℝ => Δt * ‖A‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using hid.mul_const ‖A‖
    exact h.eventually_le_const (by norm_num)
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with Δt hΔt1 hAn hmem
  have hΔtpos : (0:ℝ) < Δt := hmem
  have hx0 : (0:ℝ) ≤ Δt * ‖A‖ := mul_nonneg hΔtpos.le (norm_nonneg _)
  have hnorm : ‖Δt • A‖ = Δt * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hΔtpos]
  have hηnn : (0:ℝ) ≤ (η:ℝ) := Nat.cast_nonneg η
  have hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    rw [hnorm, div_lt_one (by positivity)]
    linarith
  -- the exponential's remainder, at the order `Lemma 1` gives it
  have hERB : MatExp.expRemainderBound (Δt • A) η ≤ CE * Δt := by
    have hq : Δt * ‖A‖ / ((η:ℝ) + 2) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (η:ℝ) + 2)]
      linarith
    have hd : (0:ℝ) < 1 - Δt * ‖A‖ / ((η:ℝ) + 2) := by linarith
    have hprod : (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹ * (1 - Δt * ‖A‖ / ((η:ℝ) + 2)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hd)
    have hinv : (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹ ≤ 2 := by
      nlinarith [inv_nonneg.mpr hd.le]
    -- one power of the step survives the `η + 1` the numerator carries
    have hpow : (Δt * ‖A‖) ^ (η + 1) ≤ Δt * ‖A‖ ^ (η + 1) := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg A) _)
      calc Δt ^ (η + 1) = Δt ^ η * Δt := by ring
        _ ≤ 1 * Δt := mul_le_mul_of_nonneg_right (pow_le_one₀ hΔtpos.le hΔt1) hΔtpos.le
        _ = Δt := one_mul _
    have hfac : (0:ℝ) < (Nat.factorial (η + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (η + 1)
    rw [MatExp.expRemainderBound, hnorm, hCEdef]
    calc (Δt * ‖A‖) ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
          * (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹
        ≤ Δt * ‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) * 2 :=
          mul_le_mul (by gcongr) hinv (inv_nonneg.mpr hd.le) (by positivity)
      _ = 2 * (‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * Δt := by ring
  -- the correction's own finite part, second order in the step
  have hexpx : Real.exp (Δt * ‖A‖) ≤ Real.exp 1 := Real.exp_le_exp.mpr hAn
  have haux : Real.exp (Δt * ‖A‖) - 1 ≤ (Δt * ‖A‖) * Real.exp (Δt * ‖A‖) := by
    have h := Real.add_one_le_exp (-(Δt * ‖A‖))
    have hmul : (-(Δt * ‖A‖) + 1) * Real.exp (Δt * ‖A‖)
        ≤ Real.exp (-(Δt * ‖A‖)) * Real.exp (Δt * ‖A‖) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    linarith
  have hquad : Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖
      ≤ (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) := by
    linarith [mul_le_mul_of_nonneg_left haux hx0]
  -- second order in the step is under first order once the step is itself under one
  have hsq : (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) ≤ Δt * (‖A‖ ^ 2 * Real.exp 1) := by
    have hd2 : Δt ^ 2 ≤ Δt :=
      calc Δt ^ 2 = Δt * Δt := pow_two Δt
        _ ≤ 1 * Δt := mul_le_mul_of_nonneg_right hΔt1 hΔtpos.le
        _ = Δt := one_mul Δt
    calc (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) = Δt ^ 2 * (‖A‖ ^ 2 * Real.exp (Δt * ‖A‖)) := by
          ring
      _ ≤ Δt ^ 2 * (‖A‖ ^ 2 * Real.exp 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpx (sq_nonneg _)) (sq_nonneg Δt)
      _ ≤ Δt * (‖A‖ ^ 2 * Real.exp 1) := mul_le_mul_of_nonneg_right hd2 (by positivity)
  have hρF : Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ + MatExp.expRemainderBound (Δt • A) η
      ≤ cF * Δt := by rw [hcFdef]; linarith [hquad.trans hsq]
  -- the integrated correction pays one `Δt` up front, so its own factors need only be bounded
  have hρG : Δt * (Real.exp (Δt * ‖A‖) - 1) + Δt * MatExp.expRemainderBound (Δt • A) η
      ≤ cG * Δt := by
    have h1 : Δt * (Real.exp (Δt * ‖A‖) - 1) ≤ Δt * (Real.exp 1 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hΔtpos.le
    have h2 : Δt * MatExp.expRemainderBound (Δt • A) η ≤ Δt * CE := by
      refine mul_le_mul_of_nonneg_left (hERB.trans ?_) hΔtpos.le
      calc CE * Δt ≤ CE * 1 := mul_le_mul_of_nonneg_left hΔt1 hCE0
        _ = CE := mul_one CE
    rw [hcGdef]; linarith
  -- and the generators the step moves
  have hgen : (n:ℝ) * (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * ∑ l, ∑ j, |H.G l j|
      ≤ (n:ℝ) * (Δt * (‖A‖ * Real.exp 1)) * ∑ l, ∑ j, |H.G l j| := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)) hSumG
    calc Δt * ‖A‖ * Real.exp (Δt * ‖A‖) ≤ Δt * ‖A‖ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hexpx hx0
      _ = Δt * (‖A‖ * Real.exp 1) := by ring
  refine (MatExp.affineDynamicsError_le A H ũ hΔtpos.le hε).trans ?_
  rw [MatExp.affineDynamicsErrorBound]
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hρF hSumH)
      (mul_le_mul_of_nonneg_right hρG hSumU)) (by positivity))
    (mul_le_mul_of_nonneg_left hgen (Real.sqrt_nonneg _))) (le_of_eq (by ring))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
