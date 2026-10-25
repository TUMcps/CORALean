module

public import CORALean.Global.ShenmaierVertex
public import CORALean.Global.ShenmaierHalfspace
public import CORALean.Global.ThetaUniform
public import CORALean.Global.L1BallOrthantVolume
public import CORALean.ContSet.Zonotope.Real.Theorems.IsGreatestCoeffNormCorner
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# Vertex sampling's accuracy for a zonotope inbody, at a fixed `ε`

`[1, Thm. 4.6]`, second half, as it holds at `p = ∞` (a zonotope `Ê`, the supremum norm on its
coefficients): for every fixed `ε ∈ (0, 1]`, `r_Svs` reaches `(1 - ε) r(Ê, E)` with probability at
least `P_S(ε)`, in dimension `m` of the coefficients. The samples `vᵢ` are `ϑ`-uniform on
`B₁ = B_{p*}`; a maximizer `zᵢ` of `zᵀvᵢ` over the cube is `sign(vᵢ)` whenever no coordinate of
`vᵢ` vanishes, so a sample in the open orthant of the optimal corner returns it (probability
`2⁻ᵐ - ϑ`, `l1Ball_orthant_volume`), and `2⁻ᵐ ≥ (ε/(2+ε))ᵐ`. The printed `P_Svs` as a
probability that `Ê ⊆ E` is false (`shenmaierVertex_counterexample`); other `p` are open.

## Inputs
* `G` – generator map
* `c` – center
* `d` – offset
* `H` – linear map
* `r` – greatest coefficient norm
* `vol` – Haar measure on the coefficients
* `Ω` – sample space
* `P` – probability measure
* `v` – random samples
* `ϑ` – uniformity parameter
* `z` – sign vectors
* `ε` – tolerance

## Hypotheses
* `hH` – `H` surjective
* `hr` – `r` is the greatest norm over the unit ball
* `hN` – at least one sample
* `hvm` – samples measurable
* `hind` – samples independent
* `hϑ` – parameter nonnegative
* `hunif` – samples nearly uniform on the cross-polytope
* `hz` – sign vectors bounded by one
* `hzv` – sign vectors align with the samples
* `hε` – tolerance positive
* `hε1` – tolerance at most one

## Conclusion
* the vertex value reaches `(1 - ε) r` with at least the stated probability

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC), 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory ProbabilityTheory CORALean

variable {n m N : ℕ} {E₂ : Type} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.shenmaierVertex_prob (G : Vec ℝ m →ₗ[ℝ] Vec ℝ n) (c d : Vec ℝ n)
    (H : E₂ →ₗ[ℝ] Vec ℝ n) (hH : Function.Surjective H) {r : ℝ}
    (hr : IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1) r)
    (vol : Measure (Vec ℝ m)) [vol.IsAddHaarMeasure] {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hN : 0 < N) (v : Fin N → Ω → Vec ℝ m)
    (hvm : ∀ i, Measurable (v i)) (hind : iIndepFun v P) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (hunif : ∀ i, IsThetaUniform P (v i) vol {x | ∑ j, |x j| ≤ 1} ϑ)
    (z : Fin N → Ω → Vec ℝ m) (hz : ∀ i ω, ‖z i ω‖ ≤ 1)
    (hzv : ∀ i ω, ∑ j, z i ω j * v i ω j = ∑ j, |v i ω j|) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : -- --- CONCL ---
    ENNReal.ofReal (shenmaierProb m N ϑ ε)
      ≤ P {ω | (1 - ε) * r ≤ shenmaierVertexValue G c H d hN fun i => z i ω} := by -- --- PROOF ---
  -- the maximum is attained at a corner `c + G s` of the cube
  let Z : Zonotope (Vec ℝ n) := ⟨m, c, fun j => G (fun k => if j = k then 1 else 0)⟩
  have hcorner : ∀ σ : Fin Z.h → Bool, Z.corner σ = c + G (fun j => if σ j then 1 else -1) :=
    fun σ => by
      simp only [Zonotope.corner, Z]
      rw [LinearMap.pi_apply_eq_sum_univ G (fun j => if σ j then (1:ℝ) else -1)]
  -- the zonotope is the set `c + G B_∞` the radius is taken over
  have hZ : Z.construct = {x | ∃ α : Vec ℝ m, ‖α‖ ≤ 1 ∧ x = c + G α} := by
    ext x
    constructor
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨β, (pi_norm_le_iff_of_nonneg zero_le_one).mpr hβ, ?_⟩
      rw [LinearMap.pi_apply_eq_sum_univ G β]
    · rintro ⟨α, hα, rfl⟩
      refine ⟨α, (pi_norm_le_iff_of_nonneg zero_le_one).mp hα, ?_⟩
      rw [LinearMap.pi_apply_eq_sum_univ G α]
  -- so `r` is the value at a corner `σ`
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun σ => coeffNorm H (Z.corner σ - d)
  have hrσ : r = coeffNorm H (c + G (fun j => if σ j then 1 else -1) - d) := by
    have hset : (fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1
        = (fun p => coeffNorm H (p - d)) '' Z.construct := by
      rw [hZ]
      ext t
      constructor
      · rintro ⟨α, hα, rfl⟩
        exact ⟨c + G α, ⟨α, by simpa using hα, rfl⟩, by simp only [add_comm c]⟩
      · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
        exact ⟨α, by simpa using hα, by simp only [add_comm c]⟩
    rw [hset] at hr
    rw [(hr.unique (Zonotope.isGreatest_coeffNorm_corner Z H hH d)), hσ, hcorner]
  have hr0 : 0 ≤ r := hrσ ▸ coeffNorm_nonneg H _
  -- the open orthant of the signs `s` in the `ℓ₁` ball
  set s : Fin m → ℝ := fun j => if σ j then 1 else -1 with hs
  have hs1 : ∀ j, s j = 1 ∨ s j = -1 := fun j => by cases h : σ j <;> simp [hs, h]
  set K : Set (Vec ℝ m) := {x | ∑ j, |x j| ≤ 1} with hK
  set S : Set (Vec ℝ m) := {x | (∑ j, |x j|) ≤ 1 ∧ ∀ j, 0 < s j * x j} with hS
  have hvol : vol S * 2 ^ m = vol K := l1Ball_orthant_volume vol s hs1
  -- the ball has finite positive volume
  have hKfin : vol K ≠ ⊤ := by
    refine ne_top_of_le_ne_top (isCompact_closedBall (0 : Vec ℝ m) 1).measure_lt_top.ne
      (measure_mono fun x hx => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    exact (Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans hx
  -- (the ball contains a small open ball around `0`)
  have hKpos : 0 < vol K := by
    refine lt_of_lt_of_le (Metric.isOpen_ball.measure_pos vol
      (⟨0, Metric.mem_ball_self (by positivity : (0 : ℝ) < 1 / (m + 1))⟩ :
        (Metric.ball (0 : Vec ℝ m) (1 / (m + 1))).Nonempty)) (measure_mono fun x hx => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hj : ∀ j, |x j| ≤ 1 / (m + 1) := fun j =>
      ((norm_le_pi_norm x j).trans hx.le : ‖x j‖ ≤ _)
    calc ∑ j, |x j| ≤ ∑ _j : Fin m, 1 / ((m : ℝ) + 1) := Finset.sum_le_sum fun j _ => hj j
      _ = m * (1 / ((m : ℝ) + 1)) := by simp
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  -- each sample lands in the orthant with probability at least `2⁻ᵐ - ϑ`
  have hSm : MeasurableSet S := by
    refine (isClosed_le (continuous_finsetSum _ fun j _ => (continuous_apply j).abs)
      continuous_const).measurableSet.inter ?_
    have : IsOpen {x : Vec ℝ m | ∀ j, 0 < s j * x j} := by
      simp_rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
        (continuous_const.mul (continuous_apply j))
    exact this.measurableSet
  have hratio : (vol S).toReal / (vol K).toReal = 1 / 2 ^ m := by
    have h1 : (vol S).toReal * 2 ^ m = (vol K).toReal := by
      rw [← hvol, ENNReal.toReal_mul]; simp
    have h2 : 0 < (vol K).toReal := ENNReal.toReal_pos hKpos.ne' hKfin
    rw [div_eq_div_iff h2.ne' (by positivity)]
    linarith [h1]
  -- so each sample lands in the orthant with probability at least `2⁻ᵐ - ϑ`
  have hP : ∀ i, 1 / 2 ^ m - ϑ ≤ P.real (v i ⁻¹' S) := fun i => by
    have := (hunif i).2 S (fun x hx => hx.1) hSm
    rw [hratio] at this
    have := (abs_le.mp this).1
    simp only [Measure.real]
    linarith
  -- a sample in the orthant has the corner `s` as its maximizer, which attains `r`
  have hevent : ∀ i ω, v i ω ∈ S → (1 - ε) * r ≤
      shenmaierVertexValue G c H d hN fun i => z i ω := fun i ω hω => by
    have hle : ∀ j, z i ω j * v i ω j ≤ |v i ω j| := fun j => by
      calc z i ω j * v i ω j ≤ |z i ω j * v i ω j| := le_abs_self _
        _ = |z i ω j| * |v i ω j| := abs_mul _ _
        _ ≤ 1 * |v i ω j| := mul_le_mul_of_nonneg_right
            ((norm_le_pi_norm (z i ω) j).trans (hz i ω)) (abs_nonneg _)
        _ = |v i ω j| := one_mul _
    have heq := (Finset.sum_eq_sum_iff_of_le fun j _ => hle j).mp (hzv i ω)
    have hzs : z i ω = s := funext fun j => by
      have hpos := hω.2 j
      have habs : |v i ω j| = s j * v i ω j := by
        rw [← abs_of_pos hpos, abs_mul]
        rcases hs1 j with h | h <;> simp [h]
      have hj := heq j (Finset.mem_univ j)
      rw [habs] at hj
      have hv0 : v i ω j ≠ 0 := fun h => by simp [h] at hpos
      exact mul_right_cancel₀ hv0 hj
    -- the corner's value is `r`, and the maximum is above it
    have hge : r ≤ shenmaierVertexValue G c H d hN fun i => z i ω := by
      refine le_trans ?_ (Finset.le_sup' (fun i => coeffNorm H (G (z i ω) + c - d))
        (Finset.mem_univ i))
      rw [hzs, hrσ, add_comm c]
    nlinarith
  -- the samples are independent, so all miss the orthant with probability at most `(1 - q)ᴺ`
  have hmeas : ∀ i, MeasurableSet (v i ⁻¹' Sᶜ) := fun i => (hvm i) hSm.compl
  have hind' : P (⋂ i, v i ⁻¹' Sᶜ) = ∏ i, P (v i ⁻¹' Sᶜ) := by
    have := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => Sᶜ) fun i _ => hSm.compl
    simpa using this
  have hmiss : P.real (⋂ i, v i ⁻¹' Sᶜ) ≤ (1 - (1 / 2 ^ m - ϑ)) ^ N := by
    rw [Measure.real, hind', ENNReal.toReal_prod]
    calc ∏ i, (P (v i ⁻¹' Sᶜ)).toReal ≤ ∏ _i : Fin N, (1 - (1 / 2 ^ m - ϑ)) := by
          refine Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
          rw [← Measure.real, Set.preimage_compl, probReal_compl_eq_one_sub (hvm i hSm)]
          linarith [hP i]
      _ = _ := by simp
  -- the event contains the union of the samples' hits
  have hsub : (⋂ i, v i ⁻¹' Sᶜ)ᶜ ⊆ {ω | (1 - ε) * r ≤
      shenmaierVertexValue G c H d hN fun i => z i ω} := fun ω hω => by
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_preimage, not_forall, not_not] at hω
    obtain ⟨i, hi⟩ := hω
    exact hevent i ω hi
  refine le_trans ?_ (measure_mono hsub)
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [← Measure.real, probReal_compl_eq_one_sub (MeasurableSet.iInter hmeas)]
  -- `P_S(ε)` is below `1 - (1 - q)ᴺ` since `(ε / (2 + ε))ᵐ ≤ 2⁻ᵐ`
  have h1 : (ε / (2 + ε)) ^ m ≤ 1 / 2 ^ m := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ (by positivity)]; nlinarith) _
  have h2 : (0 : ℝ) ≤ 1 - (1 / 2 ^ m - ϑ) := by
    have : 1 / (2 : ℝ) ^ m ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 ^ m)]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have h3 : 1 - (1 / 2 ^ m - ϑ) ≤ 1 - (ε / (2 + ε)) ^ m + ϑ := by linarith
  have := pow_le_pow_left₀ h2 h3 N
  simp only [shenmaierProb]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
