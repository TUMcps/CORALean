module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableOfMemBounded
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# A closed set that holds the dominated runs holds the run

The error set `E` of CORA's abstraction-error loop has a linear reach set `K` (input
`V = f(z✱) ⊕ B(U - u✱) ⊕ E`) over which the field less `A (x - x✱)` is in `V`. That the run stays in
`K` is not a first-exit argument alone (`ẋ = 3|x|^{2/3}` leaves `{0}`): with the field Lipschitz in
the state near `K`, a measurable `ε`-nearest point `w` of `V` to the run's field makes a linear run
`z ∈ K` with `‖x - z‖ ≤ C ε` by Gronwall, `C` free of `ε`, and `K` is closed. A continuous induction
over the window supplies the neighborhood `N` the Lipschitz bound needs.

## Inputs
* `sys` – system
* `Δt` – window length
* `R` – start set
* `V` – input set of the linear step
* `K` – set holding the dominated runs
* `N` – neighborhood of `K`
* `U` – input set
* `A` – state matrix
* `xs` – expansion point
* `L` – Lipschitz constant
* `x` – state signal
* `u` – input signal
* `y` – output signal

## Hypotheses
* `hΔt` – window length nonnegative
* `hVb` – `V` bounded
* `hVne` – `V` nonempty
* `hKc` – `K` closed
* `hKN` – unit balls around `K` lie in `N`
* `hL0` – `L` nonnegative
* `hL` – the field is `L`-Lipschitz in the state on `N`
* `hdom` – `K` holds every run of every system whose field less `A (x - x✱)` stays in `V`
* `hK` – the field of `sys` less `A (x - x✱)` lies in `V` on `K`
* `traj` – `x` is a run of `sys` from `R` under inputs in `U`

## Conclusion
* the run stays in `K`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory Set Matrix ContSetLike intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A measurable map into `V` that is within `ε` of the nearest point of `V`. -/
private theorem aux_exists_selection {V : Set (Vec ℝ n)} (hV : V.Nonempty) {ε : ℝ}
    (hε : 0 < ε) : -- --- CONCL ---
    ∃ ρ : Vec ℝ n → Vec ℝ n, Measurable ρ ∧ (∀ v, ρ v ∈ V) ∧
      ∀ v, ∀ p ∈ V, ‖v - ρ v‖ ≤ ‖v - p‖ + ε := by -- --- PROOF ---
  classical
  haveI : Nonempty V := hV.to_subtype
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq V
  have hex : ∀ v : Vec ℝ n, ∃ j, dist v (g j : Vec ℝ n) < Metric.infDist v V + ε := by
    intro v
    obtain ⟨p, hp, hvp⟩ := (Metric.infDist_lt_iff hV).mp (show Metric.infDist v V <
      Metric.infDist v V + ε / 2 by linarith)
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hg ⟨p, hp⟩ (ε / 2) (by linarith)
    refine ⟨j, ?_⟩
    have := dist_triangle v p (g j : Vec ℝ n)
    rw [Subtype.dist_eq] at hj
    simp only at hj
    linarith
  -- the index of the first near point is a measurable function of `v`
  have hmeas : ∀ j, MeasurableSet {v : Vec ℝ n | dist v (g j : Vec ℝ n) < Metric.infDist v V + ε} :=
    fun j => measurableSet_lt (continuous_id.dist continuous_const).measurable
      ((Metric.continuous_infDist_pt V).measurable.add_const ε)
  refine ⟨fun v => (g (Nat.find (hex v)) : Vec ℝ n), ?_, fun v => (g _).2, fun v p hp => ?_⟩
  · exact (measurable_from_top (f := fun j => (g j : Vec ℝ n))).comp
      (measurable_find hex hmeas)
  · have h1 := Nat.find_spec (hex v)
    have h2 := Metric.infDist_le_dist_of_mem (x := v) hp
    rw [dist_eq_norm] at h1 h2
    simp only
    linarith


/-- A measurable input in `V` gives a dominated run of the linear system from the run's start. -/
private theorem aux_dominated_run {Δt : ℝ} (hΔt : 0 ≤ Δt) {R V K : Set (Vec ℝ n)} (A : Mat ℝ n n)
    (xs : Vec ℝ n) (hVb : Bornology.IsBounded V)
    (hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
        (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
        sys'.IsTrajectory (S := ExactSet) (Icc 0 Δt) R U' x' u' y' →
        (∀ t ∈ Icc 0 Δt, sys'.f (x' t) (u' t) - A *ᵥ (x' t - xs) ∈ V) →
        ∀ t ∈ Icc 0 Δt, x' t ∈ K)
    {x0 : Vec ℝ n} (hx0 : x0 ∈ R) {w : ℝ → Vec ℝ n} (hw : ∀ t ∈ Icc 0 Δt, w t ∈ V)
    (hwm : AEStronglyMeasurable w (volume.restrict (Icc 0 Δt))) : -- --- CONCL ---
    ∃ z : ℝ → Vec ℝ n, (∀ t ∈ Icc 0 Δt, z t ∈ K) ∧ ContinuousOn z (Icc 0 Δt) ∧ z 0 = x0 ∧
      (∀ t ∈ Icc 0 Δt, z t = x0 + ∫ s in (0:ℝ)..t, (A *ᵥ (z s - xs) + w s)) ∧
      ∀ t ∈ Icc 0 Δt,
        IntervalIntegrable (fun s => A *ᵥ (z s - xs) + w s) volume 0 t := by -- --- PROOF ---
  -- the linear system `ż = A z`, whose closed form with input `w` is the candidate run
  let lin : LinearSys ℝ n := ⟨n, n, n, n, A, 0, 0, 0, 0, 0, 0, 0⟩
  set c : ℝ → Vec ℝ n := lin.closedForm (x0 - xs) w with hc
  have hcont : ContinuousOn c (Icc 0 Δt) :=
    lin.closedForm_continuousOn (S := ExactSet) (U := V) (x0 - xs) hΔt hVb hw hwm
  have hflow : ∀ t ∈ Icc 0 Δt, c t = c 0 + ∫ ρ in (0:ℝ)..t, (A *ᵥ c ρ + w ρ) :=
    fun t ht => lin.closedForm_flow (S := ExactSet) (U := V) (x0 - xs) hΔt hVb hw hwm ht
  have hc0 : c 0 = x0 - xs := lin.closedForm_zero _ _
  have hz0 : xs + c 0 = x0 := by rw [hc0]; abel
  have hzsub : ∀ s, xs + c s - xs = c s := fun s => by abel
  -- the shifted closed form satisfies the integral equation of `sys'`
  have hzflow : ∀ t ∈ Icc 0 Δt, xs + c t = x0 + ∫ s in (0:ℝ)..t, (A *ᵥ (xs + c s - xs) + w s) := by
    intro t ht
    simp only [hzsub]
    rw [hflow t ht, hc0]; abel
  -- it is a run of the system `ż = A (z - x✱) + w`, dominated by construction
  let sys' : NonlinearSys n n := ⟨fun z w => A *ᵥ (z - xs) + w, 0, fun _ _ => 0⟩
  -- its field is integrable on the window
  have hint : ∀ t ∈ Icc 0 Δt, IntervalIntegrable (fun s => A *ᵥ c s + w s) volume 0 t := by
    intro t ht
    -- the state part is continuous and the input part bounded and measurable
    have h1 : IntervalIntegrable (fun s => A *ᵥ c s) volume 0 t := by
      have : ContinuousOn (fun s => A *ᵥ c s) (Icc 0 t) :=
        ((Matrix.mulVecLin A).continuous_of_finiteDimensional.comp_continuousOn
          (hcont.mono (Icc_subset_Icc_right ht.2)))
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
      exact this.integrableOn_Icc
    -- the input is bounded and measurable
    have h2 : IntervalIntegrable w volume 0 t :=
      intervalIntegrable_of_mem_bounded (S := ExactSet) (U := V) ht.1 hVb
        (fun s hs => hw s (Icc_subset_Icc_right ht.2 hs))
        (hwm.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl))
    exact h1.add h2
  -- the shifted closed form is a run of `sys'` from the run's start
  have htraj : sys'.IsTrajectory (S := ExactSet) (Icc 0 Δt) R V (fun t => xs + c t) w
      (fun _ => 0) := by
    refine ⟨by simp only [hz0]; exact hx0, hw, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · have hAc : ContinuousOn (fun s => A *ᵥ c s) (Icc 0 Δt) :=
        (Matrix.mulVecLin A).continuous_of_finiteDimensional.comp_continuousOn hcont
      have := (hAc.aestronglyMeasurable measurableSet_Icc).add hwm
      show AEStronglyMeasurable (fun t => A *ᵥ (xs + c t - xs) + w t) _
      simp only [hzsub]
      exact this
    · intro t ht
      simpa [sys', hzsub] using hint t ht
    · exact continuousOn_const.add hcont
    · intro t ht
      simpa [sys', hz0, hzsub] using hzflow t ht
  -- the run is dominated, so it is in `K`
  refine ⟨fun t => xs + c t, ?_, continuousOn_const.add hcont, hz0, hzflow, ?_⟩
  · exact hdom n sys' V _ w (fun _ => 0) htraj (fun t ht => by simpa [sys', hzsub] using hw t ht)
  · intro t ht
    simpa [hzsub] using hint t ht


/-- The Gronwall bound is linear in `ε` and at most `ε * Γ` on the window. -/
private theorem aux_gronwall_le {c ε Δt t : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (htΔ : t ≤ Δt) : -- --- CONCL ---
    gronwallBound 0 c ε t ≤
      ε * (if c = 0 then Δt else (Real.exp (c * Δt) - 1) / c) := by -- --- PROOF ---
  unfold gronwallBound
  by_cases h0 : c = 0
  · simp only [h0, if_true, zero_add]
    exact mul_le_mul_of_nonneg_left htΔ hε
  · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm h0)
    simp only [h0, if_false, zero_mul, zero_add]
    have hexp : Real.exp (c * t) ≤ Real.exp (c * Δt) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htΔ hc)
    calc ε / c * (Real.exp (c * t) - 1) = ε * ((Real.exp (c * t) - 1) / c) := by ring
      _ ≤ ε * ((Real.exp (c * Δt) - 1) / c) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hpos.le) hε


/-- On `[0, T₀]`, where the run is in `N`, it is within `C ε` of the set, for every `ε`. -/
private theorem aux_estimate {sys : NonlinearSys n m} {Δt : ℝ} (hΔt : 0 ≤ Δt)
    {R V K N : Set (Vec ℝ n)} {U : Set (Vec ℝ m)} (A : Mat ℝ n n) (xs : Vec ℝ n)
    (hVb : Bornology.IsBounded V) (hVne : V.Nonempty) (hKN : K ⊆ N)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ N, ∀ y' ∈ N, ∀ v ∈ U, ‖sys.f y v - sys.f y' v‖ ≤ L * ‖y - y'‖)
    (hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
        (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
        sys'.IsTrajectory (S := ExactSet) (Icc 0 Δt) R U' x' u' y' →
        (∀ t ∈ Icc 0 Δt, sys'.f (x' t) (u' t) - A *ᵥ (x' t - xs) ∈ V) →
        ∀ t ∈ Icc 0 Δt, x' t ∈ K)
    (hK : ∀ y ∈ K, ∀ v ∈ U, sys.f y v - A *ᵥ (y - xs) ∈ V)
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) (Icc 0 Δt) R U x u y)
    {T₀ : ℝ} (hT₀ : T₀ ∈ Icc 0 Δt) (hxN : ∀ s ∈ Icc 0 T₀, x s ∈ N) {ε : ℝ}
    (hε : 0 < ε) : -- --- CONCL ---
    ∀ t ∈ Icc 0 T₀, ∃ k ∈ K, ‖x t - k‖ ≤
      (((2 * ‖A‖ + L) * Δt * (if 2 * ‖A‖ + L = 0 then Δt else
        (Real.exp ((2 * ‖A‖ + L) * Δt) - 1) / (2 * ‖A‖ + L))) + Δt) * ε := by -- --- PROOF ---
  set a := ‖A‖ with ha
  set c := 2 * a + L with hc
  have ha0 : 0 ≤ a := norm_nonneg _
  have hc0 : 0 ≤ c := by positivity
  have hΔT : T₀ ≤ Δt := hT₀.2
  have hsub : Icc 0 T₀ ⊆ Icc 0 Δt := Icc_subset_Icc_right hΔT
  -- the signal and its nearest-point selection
  set v : ℝ → Vec ℝ n := fun s => sys.f (x s) (u s) - A *ᵥ (x s - xs) with hv
  obtain ⟨ρ, hρm, hρV, hρ⟩ := aux_exists_selection hVne hε
  set w : ℝ → Vec ℝ n := fun s => ρ (v s) with hw
  have hAc : ContinuousOn (fun s => A *ᵥ (x s - xs)) (Icc 0 Δt) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional.comp_continuousOn
      (traj.cont.sub continuousOn_const)
  have hvm : AEStronglyMeasurable v (volume.restrict (Icc 0 Δt)) :=
    traj.meas.sub (hAc.aestronglyMeasurable measurableSet_Icc)
  have hwm : AEStronglyMeasurable w (volume.restrict (Icc 0 Δt)) :=
    (hρm.comp_aemeasurable hvm.aemeasurable).aestronglyMeasurable
  obtain ⟨z, hzK, hzc, hz0, hzflow, hzint⟩ := aux_dominated_run hΔt A xs hVb hdom
    traj.init (w := w) (fun s _ => hρV _) hwm
  -- the error and the integrand it integrates
  set e : ℝ → Vec ℝ n := fun s => x s - z s with he
  set g : ℝ → Vec ℝ n := fun s => sys.f (x s) (u s) - (A *ᵥ (z s - xs) + w s) with hg
  have hec : ContinuousOn e (Icc 0 Δt) := traj.cont.sub hzc
  have heflow : ∀ t ∈ Icc 0 Δt, e t = ∫ s in (0:ℝ)..t, g s := by
    intro t ht
    have h1 := traj.flow t ht
    have h2 := hzflow t ht
    show x t - z t = _
    rw [h1, h2, add_sub_add_left_eq_sub]
    exact (intervalIntegral.integral_sub (traj.integrable t ht) (hzint t ht)).symm
  -- the integrand is bounded by `c ‖e‖ + ε`
  have hgb : ∀ s ∈ Icc 0 T₀, ‖g s‖ ≤ c * ‖e s‖ + ε := by
    intro s hs
    have hsΔ := hsub hs
    have hxs := hxN s hs
    have hzs : z s ∈ K := hzK s hsΔ
    have hu : u s ∈ U := traj.input s hsΔ
    -- the point of `K` under `x s` has its field in `V`, and the Lipschitz bound moves it
    have hp := hK (z s) hzs (u s) hu
    have hr := hρ (v s) _ hp
    have hLip := hL (x s) hxs (z s) (hKN hzs) (u s) hu
    -- the linear parts are bounded by `‖A‖`
    have hA1 : ‖A *ᵥ (x s - z s)‖ ≤ a * ‖x s - z s‖ := Matrix.linfty_opNorm_mulVec A _
    have hA2 : ‖A *ᵥ (e s)‖ ≤ a * ‖e s‖ := Matrix.linfty_opNorm_mulVec A _
    -- `v s - p = (f(x) - f(z)) - A (x - z)`
    have hvp : v s - (sys.f (z s) (u s) - A *ᵥ (z s - xs)) =
        (sys.f (x s) (u s) - sys.f (z s) (u s)) - A *ᵥ (x s - z s) := by
      simp only [hv, Matrix.mulVec_sub]
      abel
    have hvpn : ‖v s - (sys.f (z s) (u s) - A *ᵥ (z s - xs))‖ ≤ L * ‖e s‖ + a * ‖e s‖ := by
      rw [hvp]
      refine (norm_sub_le _ _).trans ?_
      exact add_le_add hLip hA1
    have hgeq : g s = A *ᵥ (e s) + (v s - w s) := by
      simp only [hg, hv, he, hw, Matrix.mulVec_sub]
      abel
    -- split the integrand into the linear part and the selection's error
    rw [hgeq]
    calc ‖A *ᵥ (e s) + (v s - w s)‖ ≤ ‖A *ᵥ (e s)‖ + ‖v s - w s‖ := norm_add_le _ _
      _ ≤ a * ‖e s‖ + ((L * ‖e s‖ + a * ‖e s‖) + ε) := by
        refine add_le_add hA2 ?_
        have h3 : ‖v s - w s‖ = ‖v s - ρ (v s)‖ := rfl
        rw [h3]
        linarith
      _ = c * ‖e s‖ + ε := by simp only [hc]; ring
  -- the integral of the error's norm, which Gronwall's lemma bounds
  set E : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, ‖e s‖ with hE
  have hen : ContinuousOn (fun s => ‖e s‖) (Icc 0 Δt) := hec.norm
  have hEint : ∀ t ∈ Icc 0 Δt, IntervalIntegrable (fun s => ‖e s‖) volume 0 t := fun t ht =>
    (hen.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)).intervalIntegrable
  have hbound : ∀ t ∈ Icc 0 T₀, ‖e t‖ ≤ c * E t + ε * t := by
    intro t ht
    have htΔ := hsub ht
    rw [heflow t htΔ]
    have hci : IntervalIntegrable (fun s => c * ‖e s‖) volume 0 t := (hEint t htΔ).const_mul c
    have hcint : IntervalIntegrable (fun s => c * ‖e s‖ + ε) volume 0 t :=
      hci.add intervalIntegrable_const
    refine (intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Filter.Eventually.of_forall fun s hs => hgb s ⟨hs.1.le, hs.2.trans ht.2⟩) hcint).trans ?_
    rw [intervalIntegral.integral_add hci intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [hE, smul_eq_mul, sub_zero]
    exact le_of_eq (by ring)
  -- Gronwall's lemma on `E`, whose derivative is `‖e‖`
  have hEc : ContinuousOn E (Icc 0 T₀) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := 0) (hEint T₀ hT₀)
      (by rw [uIcc_of_le hT₀.1]; exact ⟨le_rfl, hT₀.1⟩)
    rwa [uIcc_of_le hT₀.1] at this
  -- the fundamental theorem of calculus, from the right
  have hE' : ∀ t ∈ Ico 0 T₀, HasDerivWithinAt E ‖e t‖ (Ici t) t := by
    intro t ht
    have htΔ : t ∈ Icc 0 Δt := ⟨ht.1, ht.2.le.trans hΔT⟩
    haveI : Fact (t ∈ Icc 0 Δt) := ⟨htΔ⟩
    have h1 : HasDerivWithinAt E ‖e t‖ (Icc 0 Δt) t :=
      intervalIntegral.integral_hasDerivWithinAt_right (hEint t htΔ)
        (hen.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hen t htΔ)
    exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hΔT⟩)
  have hEnn : ∀ t ∈ Icc 0 T₀, 0 ≤ E t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s _ => norm_nonneg _
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := E) (f' := fun t => ‖e t‖)
    (δ := 0) (K := c) (ε := ε * Δt) hEc hE' (by simp [hE]) (fun t ht => by
      have htT : t ∈ Icc 0 T₀ := ⟨ht.1, ht.2.le⟩
      rw [norm_norm, Real.norm_of_nonneg (hEnn t htT)]
      have := hbound t htT
      have h2 : ε * t ≤ ε * Δt := mul_le_mul_of_nonneg_left (ht.2.le.trans hΔT) hε.le
      linarith)
  intro t ht
  -- combine Gronwall's bound with the integral inequality
  refine ⟨z t, hzK t (hsub ht), ?_⟩
  have h1 := hG t ht
  rw [Real.norm_of_nonneg (hEnn t ht), sub_zero] at h1
  have h2 := aux_gronwall_le (c := c) (ε := ε * Δt) (Δt := Δt) hc0 (by positivity) (ht.2.trans hΔT)
  have h3 := hbound t ht
  have h4 : ε * t ≤ ε * Δt := mul_le_mul_of_nonneg_left (ht.2.trans hΔT) hε.le
  have h5 : c * E t ≤ c * (ε * Δt * (if c = 0 then Δt else (Real.exp (c * Δt) - 1) / c)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hc0
  show ‖e t‖ ≤ _
  nlinarith [h3, h4, h5]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A closed set holding every run of every system dominated by the linear step with input `V`
holds every run of a system whose field less `A (x - x✱)` lies in `V` on the set, if the field is
Lipschitz in the state on a neighborhood of the set. -/
theorem NonlinearSys.IsTrajectory.mem_of_fixedPoint {sys : NonlinearSys n m} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) {R V K N : Set (Vec ℝ n)} {U : Set (Vec ℝ m)} (A : Mat ℝ n n) (xs : Vec ℝ n)
    (hVb : Bornology.IsBounded V) (hVne : V.Nonempty) (hKc : IsClosed K)
    (hKN : ∀ y ∈ K, Metric.ball y 1 ⊆ N) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ N, ∀ y' ∈ N, ∀ v ∈ U, ‖sys.f y v - sys.f y' v‖ ≤ L * ‖y - y'‖)
    (hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
        (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
        sys'.IsTrajectory (S := ExactSet) (Icc 0 Δt) R U' x' u' y' →
        (∀ t ∈ Icc 0 Δt, sys'.f (x' t) (u' t) - A *ᵥ (x' t - xs) ∈ V) →
        ∀ t ∈ Icc 0 Δt, x' t ∈ K)
    (hK : ∀ y ∈ K, ∀ v ∈ U, sys.f y v - A *ᵥ (y - xs) ∈ V)
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) (Icc 0 Δt) R U x u y) : -- --- CONCL ---
    ∀ t ∈ Icc 0 Δt, x t ∈ K := by -- --- PROOF ---
  have hKN' : K ⊆ N := fun y hy => hKN y hy (Metric.mem_ball_self one_pos)
  set c := 2 * ‖A‖ + L with hc
  -- the constants of the estimate
  set Γ : ℝ := if c = 0 then Δt else (Real.exp (c * Δt) - 1) / c with hΓ
  set C : ℝ := c * Δt * Γ + Δt with hC
  have hc0 : 0 ≤ c := by positivity
  -- `Γ` is nonnegative, so `C` is
  have hΓ0 : 0 ≤ Γ := by
    by_cases h0 : c = 0
    · simp [hΓ, h0, hΔt]
    · have hpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm h0)
      simp only [hΓ, h0, if_false]
      exact div_nonneg (by linarith [Real.add_one_le_exp (c * Δt), mul_nonneg hc0 hΔt]) hpos.le
  have hC0 : 0 ≤ C := by positivity
  -- where the run is in `N`, it is in `K`
  have hclos : ∀ T₀ ∈ Icc 0 Δt, (∀ r ∈ Icc 0 T₀, x r ∈ N) → ∀ t ∈ Icc 0 T₀, x t ∈ K := by
    intro T₀ hT₀ hxN t ht
    rw [← hKc.closure_eq, Metric.mem_closure_iff]
    intro ε' hε'
    have hε : 0 < ε' / (2 * (C + 1)) := by positivity
    obtain ⟨k, hk, hkn⟩ := aux_estimate hΔt A xs hVb hVne hKN' hL0 hL hdom hK traj hT₀ hxN hε t ht
    refine ⟨k, hk, ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt hkn ?_
    rw [← hC, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the start is in `K`
  have hx0 : x 0 ∈ K := by
    obtain ⟨p, hp⟩ := hVne
    obtain ⟨z, hzK, -, hz0, -⟩ := aux_dominated_run hΔt A xs hVb hdom traj.init
      (w := fun _ => p) (fun _ _ => hp) aestronglyMeasurable_const
    rw [← hz0]
    exact hzK 0 ⟨le_rfl, hΔt⟩
  -- continuous induction on the window
  let s : Set ℝ := {t | ∀ r ∈ Icc 0 t, x r ∈ K}
  have hs : IsClosed (s ∩ Icc 0 Δt) := by
    -- a limit of times with the whole history in `K` has it too, `K` being closed
    refine isClosed_of_closure_subset fun t ht => ?_
    have htI : t ∈ Icc 0 Δt := isClosed_Icc.closure_subset (closure_mono inter_subset_right ht)
    refine ⟨fun r hr => ?_, htI⟩
    rcases hr.2.lt_or_eq with hlt | heq
    · obtain ⟨t'', ht''r, ht''s, -⟩ := mem_closure_iff_nhds.mp ht (Ioi r) (Ioi_mem_nhds hlt)
      exact ht''s r ⟨hr.1, ht''r.le⟩
    · rw [heq]
      have hcw : ContinuousWithinAt x (s ∩ Icc 0 Δt) t := (traj.cont t htI).mono inter_subset_right
      have h1 := hcw.mem_closure_image ht
      refine hKc.closure_subset_iff.mpr ?_ h1
      rintro _ ⟨t'', ⟨hs'', ht''I⟩, rfl⟩
      exact hs'' t'' ⟨ht''I.1, le_rfl⟩
  have hmain : Icc 0 Δt ⊆ s := by
    refine IsClosed.Icc_subset_of_forall_exists_gt hs (fun r hr => ?_) fun t0 ht0 y hy => ?_
    · obtain rfl : r = 0 := le_antisymm hr.2 hr.1
      exact hx0
    · obtain ⟨hs0, ht0⟩ := ht0
      have hxt0K : x t0 ∈ K := hs0 t0 ⟨ht0.1, le_rfl⟩
      obtain ⟨η, hη, hδ⟩ := Metric.continuousWithinAt_iff.mp (traj.cont t0 ⟨ht0.1, ht0.2.le⟩) 1
        one_pos
      -- a later time `t'` inside the continuity radius
      set t' := min (min y (t0 + η / 2)) Δt with ht'
      have ht'1 : t0 < t' := lt_min (lt_min hy (by linarith)) ht0.2
      have ht'Δ : t' ∈ Icc 0 Δt := ⟨by linarith [ht0.1], min_le_right _ _⟩
      have hxN : ∀ r ∈ Icc 0 t', x r ∈ N := by
        intro r hr
        by_cases hrt : r ≤ t0
        · exact hKN' (hs0 r ⟨hr.1, hrt⟩)
        · push Not at hrt
          have hrΔ : r ∈ Icc 0 Δt := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
          have hrη : r ≤ t0 + η / 2 := hr.2.trans ((min_le_left _ _).trans (min_le_right _ _))
          have hd : dist r t0 < η := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith
          exact hKN (x t0) hxt0K (by rw [Metric.mem_ball]; exact hδ hrΔ hd)
      exact ⟨t', hclos t' ht'Δ hxN,
        ⟨ht'1, (min_le_left _ _).trans (min_le_left _ _)⟩⟩
  intro t ht
  exact hmain ht t ⟨ht.1, le_rfl⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
