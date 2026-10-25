module

public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.InputTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The printed particulate reachable set of the CDC 2007 paper does not contain it

[1, Prop. 2] gives the set the input adds over a step as `(Ir + W*(r))V + Σ_{i=3}^p 𝒜ⁱr^{i+1}/
(i!(i+1)) V + E(r)rV`, one matrix `Ir + W*(r)` applied to one element of `V`, which is the
contribution of an input constant over the step. At the point matrix `A = [[0, 0], [1, 0]]`,
`A² = 0`, so `W*(r) = ½Ar²`, the sum vanishes, and `E(r)rV` is a box of half-width `O(r^{p+2})`.
For `V = [-1, 1] × {0}`, the input `v(t) = (w(t), 0)` with `w = 1` on `[0, r/2]` and `-1` after
reaches `(0, r²/4)`, which for `r ≤ 1/4` and `p ≥ 1` is not in the printed set.

## Inputs
* `η` – Taylor order `p`
* `r` – step length

## Hypotheses
* `hη` – Taylor order at least one
* `hr` – step length positive
* `hr1` – step length at most `1/4`

## Conclusion
* a point the input reaches that the printed set does not contain

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A = [[0, 0], [1, 0]]` squares to zero. -/
theorem LinearSys.aux_sq_eq_zero_lower :
    (!![0, 0; 1, 0] : Mat ℝ 2 2) ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]

/-- The flow of `A = [[0, 0], [1, 0]]` stops after its linear term: `e^{tA} = I + tA`. -/
theorem LinearSys.aux_exp_smul_lower (t : ℝ) : -- --- CONCL ---
    exp (t • (!![0, 0; 1, 0] : Mat ℝ 2 2)) = 1 + t • !![0, 0; 1, 0] := by -- --- PROOF ---
  rw [exp_eq_tsum ℝ]
  show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • (t • (!![0, 0; 1, 0] : Mat ℝ 2 2)) ^ i = _
  rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
    rw [smul_pow, pow_eq_zero_of_le (show 2 ≤ b by simp at hb; omega)
      LinearSys.aux_sq_eq_zero_lower, smul_zero, smul_zero]]
  simp [Finset.sum_range_succ]

/-- The points of `V = [-1, 1] × {0}`, coordinatewise. -/
theorem LinearSys.aux_mem_segment (x : Vec ℝ 2) : -- --- CONCL ---
    x ∈ (⟨1, 0, fun _ => ![1, 0]⟩ : Real.Zonotope (Vec ℝ 2)).construct ↔
      |x 0| ≤ 1 ∧ x 1 = 0 := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, rfl⟩
    simp
    exact hβ 0
  · rintro ⟨h0, h1⟩
    refine ⟨fun _ => x 0, fun _ => h0, ?_⟩
    ext i; fin_cases i <;> simp [h1]

/-- The sign switching at `r/2`, `1` before and `-1` after, is interval integrable. -/
theorem LinearSys.aux_sign_integrable (r a b : ℝ) : -- --- CONCL ---
    IntervalIntegrable (fun s : ℝ => if s ≤ r / 2 then (1 : ℝ) else -1)
      volume a b := by -- --- PROOF ---
  have hm : Measurable (fun s : ℝ => if s ≤ r / 2 then (1 : ℝ) else -1) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  refine (intervalIntegrable_iff.mpr ?_)
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s => by split_ifs <;> simp

/-- The switching sign integrates to `0` over `[0, r]`, and against `r - s` to `r²/4`. -/
theorem LinearSys.aux_integral_sign (r : ℝ) (hr : 0 < r) : -- --- CONCL ---
    (∫ s in (0:ℝ)..r, (if s ≤ r / 2 then (1 : ℝ) else -1)) = 0 ∧
    (∫ s in (0:ℝ)..r, (r - s) * (if s ≤ r / 2 then (1 : ℝ) else -1)) =
      r ^ 2 / 4 := by -- --- PROOF ---
  -- the sign and its product with `r - s` are integrable on every interval
  have hI := LinearSys.aux_sign_integrable r
  have hJ : ∀ a b, IntervalIntegrable
      (fun s : ℝ => (r - s) * (if s ≤ r / 2 then (1 : ℝ) else -1)) volume a b :=
    fun a b => (hI a b).continuousOn_mul (by fun_prop)
  -- on the first half the sign is `1`, on the second `-1`
  have h1 : ∀ g : ℝ → ℝ, (∫ s in (0:ℝ)..(r / 2), g s * (if s ≤ r / 2 then (1 : ℝ) else -1)) =
      ∫ s in (0:ℝ)..(r / 2), g s := fun g => by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le (by linarith)] at hs
    simp [hs.2]
  have h2 : ∀ g : ℝ → ℝ, (∫ s in (r / 2)..r, g s * (if s ≤ r / 2 then (1 : ℝ) else -1)) =
      -∫ s in (r / 2)..r, g s := fun g => by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le (by linarith)] at hs
    simp [not_le.mpr hs.1]
  -- split at `r/2`: the two halves of the sign cancel, and the weighted ones leave `r²/4`
  constructor
  · have := intervalIntegral.integral_add_adjacent_intervals (hI 0 (r / 2)) (hI (r / 2) r)
    rw [← this]
    have e1 := h1 (fun _ => 1)
    have e2 := h2 (fun _ => 1)
    simp only [one_mul] at e1 e2
    rw [e1, e2]; simp; ring
  · have := intervalIntegral.integral_add_adjacent_intervals (hJ 0 (r / 2)) (hJ (r / 2) r)
    rw [← this]
    have e1 := h1 (fun s => r - s)
    have e2 := h2 (fun s => r - s)
    have hs : ∀ a b : ℝ, ∫ s in a..b, (r - s) = r * (b - a) - (b ^ 2 - a ^ 2) / 2 :=
      fun a b => by
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => r) (g := fun s : ℝ => s)
        intervalIntegrable_const (continuous_id.intervalIntegrable a b)]
      simp [integral_id]
      ring
    rw [e1, e2, hs, hs]
    ring

/-- The `l∞` norm of `rA` is at most `r` for `A = [[0, 0], [1, 0]]`. -/
theorem LinearSys.aux_norm_smul_lower_le {r : ℝ} (hr : 0 < r) : -- --- CONCL ---
    ‖r • (!![0, 0; 1, 0] : Mat ℝ 2 2)‖ ≤ r := by -- --- PROOF ---
  rw [Matrix.linfty_opNorm_def]
  have : ((Finset.univ : Finset (Fin 2)).sup
      fun i => ∑ j, ‖(r • (!![0, 0; 1, 0] : Mat ℝ 2 2)) i j‖₊) ≤ ⟨r, hr.le⟩ := by
    apply Finset.sup_le; intro i _
    fin_cases i
    · simp
    · simp [Fin.sum_univ_two]
      rw [← NNReal.coe_le_coe]
      simp [abs_of_pos hr]
      exact le_rfl
  exact_mod_cast this

/-- The entry of `E(r)rV` at `A = [[0, 0], [1, 0]]` is at most `6r³/11`, for `r ≤ 1/4` and
`p ≥ 1`. -/
theorem LinearSys.aux_inputRemainder_lower_le {η : ℕ} (hη : 1 ≤ η) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1 / 4) : -- --- CONCL ---
    r * MatExp.expRemainderBound (r • (!![0, 0; 1, 0] : Mat ℝ 2 2)) η ≤
      6 / 11 * r ^ 3 := by -- --- PROOF ---
  -- the factors of the bound: the norm, its power, the factorial and the geometric series
  set n := ‖r • (!![0, 0; 1, 0] : Mat ℝ 2 2)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hnr : n ≤ r := LinearSys.aux_norm_smul_lower_le hr
  have hpow : n ^ (η + 1) ≤ r ^ 2 := by
    calc n ^ (η + 1) ≤ n ^ 2 := pow_le_pow_of_le_one hn0 (by linarith) (by omega)
      _ ≤ r ^ 2 := pow_le_pow_left₀ hn0 hnr 2
  have hfac : (2 : ℝ) ≤ (Nat.factorial (η + 1) : ℝ) := by
    have : Nat.factorial 2 ≤ Nat.factorial (η + 1) := Nat.factorial_le (by omega)
    exact_mod_cast this
  -- the scaled norm is at most `1/4`, so the geometric factor is at most `12/11`
  have hη2 : (3 : ℝ) ≤ (η : ℝ) + 2 := by
    have : (1 : ℝ) ≤ η := by exact_mod_cast hη
    linarith
  have hq : n / ((η : ℝ) + 2) ≤ 1 / 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hinv : (1 - n / ((η : ℝ) + 2))⁻¹ ≤ 12 / 11 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hinv0 : 0 ≤ (1 - n / ((η : ℝ) + 2))⁻¹ := inv_nonneg.mpr (by linarith)
  unfold MatExp.expRemainderBound
  rw [← hn]
  have hfrac : n ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) ≤ r ^ 2 / 2 :=
    calc n ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) ≤ r ^ 2 / (Nat.factorial (η + 1) : ℝ) :=
          div_le_div_of_nonneg_right hpow (by linarith)
      _ ≤ r ^ 2 / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hfac
  have hfrac0 : 0 ≤ n ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by positivity
  have := mul_le_mul hfrac hinv hinv0 (by positivity)
  nlinarith

/-- Two equations `r x + a y = 0` and `r² x / 2 + b y = r²/4` have no solution with `|y| ≤ 1`
and `|a|, |b| ≤ δ ≤ 6r³/11`, for `0 < r ≤ 1/4`. -/
theorem LinearSys.aux_no_solution {r δ x y a b : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4)
    (hδ : δ ≤ 6 / 11 * r ^ 3) (hy : |y| ≤ 1) (ha : |a| ≤ δ) (hb : |b| ≤ δ)
    (e0 : r * x + a * y = 0) (e1 : 2⁻¹ * r ^ 2 * x + b * y = r ^ 2 / 4) : -- --- CONCL ---
    False := by -- --- PROOF ---
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans ha
  -- the first coordinate forces `|x|` below `δ / r`
  have h1 : r * |x| ≤ δ := by
    have e : r * x = -(a * y) := by linarith
    calc r * |x| = |r * x| := by rw [abs_mul, abs_of_pos hr]
      _ = |a| * |y| := by rw [e, abs_neg, abs_mul]
      _ ≤ δ * 1 := mul_le_mul ha hy (abs_nonneg _) hδ0
      _ = δ := mul_one δ
  have h2 : |x| ≤ 6 / 11 * r ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hr
    calc r * |x| ≤ δ := h1
      _ ≤ 6 / 11 * r ^ 3 := hδ
      _ = r * (6 / 11 * r ^ 2) := by ring
  -- and the second coordinate falls short
  have h3 : |b * y| ≤ δ := by
    rw [abs_mul]
    calc |b| * |y| ≤ δ * 1 := mul_le_mul hb hy (abs_nonneg _) hδ0
      _ = δ := mul_one δ
  have h4 : 2⁻¹ * r ^ 2 * x ≤ 2⁻¹ * r ^ 2 * (6 / 11 * r ^ 2) :=
    (mul_le_mul_of_nonneg_left (le_abs_self x) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h5 : r ^ 2 / 4 ≤ 3 / 11 * r ^ 4 + 6 / 11 * r ^ 3 := by
    have := (abs_le.mp h3).2
    nlinarith
  have h6 : 3 / 11 * r ^ 2 + 6 / 11 * r < 1 / 4 := by nlinarith
  have h7 : 3 / 11 * r ^ 4 + 6 / 11 * r ^ 3 < r ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_left h6 (pow_pos hr 2)
    nlinarith
  linarith

/-- The input `(w, 0)` with `w = 1` up to `r/2` and `-1` after drives `A = [[0, 0], [1, 0]]` to
`(0, r²/4)`. -/
theorem LinearSys.aux_integral_flow (r : ℝ) (hr : 0 < r) : -- --- CONCL ---
    (![0, r ^ 2 / 4] : Vec ℝ 2) = ∫ s in (0:ℝ)..r,
      exp ((r - s) • toRealMat (LinearSys.canonical (!![0, 0; 1, 0] : Mat ℝ 2 2) :
        LinearSys ℝ 2).A) *ᵥ ![if s ≤ r / 2 then 1 else -1, 0] := by -- --- PROOF ---
  -- the integrand is `(w s, (r - s) w s)`
  simp only [toRealMat_real, LinearSys.aux_exp_smul_lower]
  have hf : ∀ s : ℝ, (1 + (r - s) • (!![0, 0; 1, 0] : Mat ℝ 2 2)) *ᵥ
      (![if s ≤ r / 2 then 1 else -1, 0] : Vec ℝ 2) =
      ![if s ≤ r / 2 then 1 else -1, (r - s) * if s ≤ r / 2 then 1 else -1] := fun s => by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [hf]
  obtain ⟨h0, h1⟩ := LinearSys.aux_integral_sign r hr
  have hint : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 r → IntegrableOn f (Set.Ioc 0 r) :=
    fun f hf => (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp hf
  have hJ : IntervalIntegrable
      (fun s : ℝ => (r - s) * (if s ≤ r / 2 then (1 : ℝ) else -1)) volume 0 r :=
    (LinearSys.aux_sign_integrable r 0 r).continuousOn_mul (by fun_prop)
  -- the vector integral is read coordinatewise
  rw [intervalIntegral.integral_of_le hr.le]
  ext i
  rw [eval_integral (fun j => by
    fin_cases j
    · exact hint _ (LinearSys.aux_sign_integrable r 0 r)
    · exact hint _ hJ)]
  fin_cases i
  · simp
    rw [← intervalIntegral.integral_of_le hr.le]; exact h0.symm
  · simp
    rw [← intervalIntegral.integral_of_le hr.le, ← h1]
    refine (intervalIntegral.integral_congr fun s _ => ?_).symm
    split_ifs <;> ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.particulateReach_printed_counterexample {η : ℕ} (hη : 1 ≤ η) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1 / 4) : -- --- CONCL ---
    let A : Mat ℝ 2 2 := !![0, 0; 1, 0]
    let sys : LinearSys ℝ 2 := LinearSys.canonical A
    let V : Real.Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ => ![1, 0]⟩
    let Wstar : Mat ℝ 2 2 := (1 / 2 * r ^ 2) • A + (1 / 6 * r ^ 3) • A ^ 2 -- W*(r)
    let printed : Set (Vec ℝ 2) :=
      (fun v => (r • 1 + Wstar) *ᵥ v) '' V.construct +
        ∑ i ∈ Finset.Icc 3 η, (fun v => sys.inputTerm r i *ᵥ v) '' V.construct +
        ⋃ M ∈ (MatExp.inputRemainder A r η).construct, (fun v => M *ᵥ v) '' V.construct
    ![0, r ^ 2 / 4] ∈ sys.inputReach (S := 𝒵) V r ∧ ![0, r ^ 2 / 4] ∉ printed := by -- --- PROOF ---
  intro A sys V Wstar printed
  refine ⟨?_, ?_⟩
  · -- the input `(w, 0)`, `w = 1` up to `r/2` and `-1` after, reaches `(0, r²/4)`
    refine ⟨fun s => ![if s ≤ r / 2 then 1 else -1, 0], fun s _ => ?_, ?_,
      LinearSys.aux_integral_flow r hr⟩
    · refine (LinearSys.aux_mem_segment _).mpr ⟨?_, rfl⟩
      beta_reduce
      simp only [Matrix.cons_val_zero]
      split_ifs <;> simp
    · refine Measurable.aestronglyMeasurable (measurable_pi_lambda _ fun i => ?_)
      fin_cases i
      · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
      · exact measurable_const
  · -- the printed set is a box of half-width `6r³/11` about the segment `{(rt, r²t/2)}`
    -- the orders from three up vanish, as `A² = 0`
    have hS2 : ∑ i ∈ Finset.Icc 3 η, (fun v => sys.inputTerm r i *ᵥ v) '' V.construct = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
      have hT : sys.inputTerm r i = 0 := by
        simp only [LinearSys.inputTerm, sys, toRealMat_real]
        rw [pow_eq_zero_of_le (show 2 ≤ i by omega) LinearSys.aux_sq_eq_zero_lower, smul_zero]
      simp only [hT, Matrix.zero_mulVec]
      ext x
      simp only [Set.mem_image, Set.mem_zero]
      exact ⟨fun ⟨_, _, h⟩ => h.symm,
        fun h => ⟨0, (LinearSys.aux_mem_segment 0).mpr (by simp), h.symm⟩⟩
    -- a point of the printed set splits into `(r I + W*) v` and the remainder box
    intro h
    simp only [printed, hS2, add_zero] at h
    obtain ⟨_, ⟨v, hv, rfl⟩, _, hc, hx⟩ := h
    simp only [Set.mem_iUnion, Set.mem_image] at hc
    obtain ⟨M, hM, w, hw, rfl⟩ := hc
    obtain ⟨hv0, hv1⟩ := (LinearSys.aux_mem_segment v).mp hv
    obtain ⟨hw0, hw1⟩ := (LinearSys.aux_mem_segment w).mp hw
    -- the remainder box has half-width `δ ≤ 6r³/11`
    have hb := LinearSys.aux_inputRemainder_lower_le hη hr hr1
    have hM00 := hM (0, 0)
    have hM10 := hM (1, 0)
    simp only [MatExp.inputRemainder] at hM00 hM10
    generalize r * MatExp.expRemainderBound (r • A) η = δ at hb hM00 hM10
    have hA2 : A ^ 2 = 0 := LinearSys.aux_sq_eq_zero_lower
    simp only [Wstar, hA2, smul_zero, add_zero] at hx
    -- the two coordinates of the point
    have hx0 := congrFun hx 0
    have hx1 := congrFun hx 1
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1, hw1] at hx0 hx1
    simp only [Entrywise.entry_mat] at hM00 hM10
    have ha : |M 0 0| ≤ δ := abs_le.mpr ⟨by linarith [hM00.1], by linarith [hM00.2]⟩
    have hb' : |M 1 0| ≤ δ := abs_le.mpr ⟨by linarith [hM10.1], by linarith [hM10.2]⟩
    exact LinearSys.aux_no_solution hr hr1 hb hw0 ha hb' hx0 hx1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
