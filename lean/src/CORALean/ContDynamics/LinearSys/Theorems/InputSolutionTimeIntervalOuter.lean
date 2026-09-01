import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable

/-!
# `inputSolution` contains the input's contribution at every time in the step

Althoff's Prop. 3.3, and what `inputSolution_outer` alone does not give:
Thm. 3.1 encloses the contribution at the *end* of a step, while a time-interval
enclosure needs one set covering every `t ∈ [0,r]` at once.

`0 ∈ U` is what makes the two the same set. The thesis argues through the
semigroup decomposition `P(r+t) = e^{Ar}P(t) ⊕ P(r)`, using `0 ∈ e^{Ar}P(t)` to
get `P(r) ⊆ P(r+t)`. Here the same hypothesis is used directly: delay the input
to the end of the step and pad the gap with the origin, which is admissible
exactly when `U` contains it, and the padded input reproduces the shorter
integral over the full step.

That the padded input is *not* a trajectory of the system does not matter —
`inputSolution_outer` asks only where the input lies and that it be measurable,
never that it solve anything.

Doing it this way avoids needing `inputSolution t η U ⊆ inputSolution r η U`,
which is not available: `plus` and `mtimes` carry enclosure guarantees, not
monotonicity, so a smaller enclosure cannot be lifted into a larger one at the
level of representations.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]

/-- The input delayed by `d`, with the origin filling the gap. Strict `<` so the
padding is exact on `Ioc 0 d` and the delay exact on `Ioc d r`, leaving no
endpoint to argue about. -/
noncomputable def aux_delay (u : ℝ → Vec ℝ n) (d : ℝ) : ℝ → Vec ℝ n :=
  fun s => if d < s then u (s - d) else 0

/-- The integrand of the shorter step, extended by zero below `0`. The delayed
input's integrand is exactly this, shifted — which is what turns an integral
over `[0,r]` into one over `[0,t]`. -/
noncomputable def aux_capped (A : Mat ℝ n n) (u : ℝ → Vec ℝ n) (t : ℝ) : ℝ → Vec ℝ n :=
  fun σ => if 0 < σ then exp ((t - σ) • A) *ᵥ u σ else 0

set_option maxHeartbeats 40000 in
/-- The delayed input's integrand, pointwise, is the shorter step's integrand
shifted by `r - t`. Exact at every real, including both endpoints, because the
two `if`s switch on the same condition. -/
theorem aux_delay_integrand (A : Mat ℝ n n) (u : ℝ → Vec ℝ n) {r t : ℝ} (s : ℝ) :
    exp ((r - s) • A) *ᵥ aux_delay u (r - t) s = aux_capped A u t (s - (r - t)) := by
  simp only [aux_delay, aux_capped]
  by_cases hs : r - t < s
  · rw [if_pos hs, if_pos (by linarith : (0:ℝ) < s - (r - t))]
    have hexp : t - (s - (r - t)) = r - s := by ring
    rw [hexp]
  · rw [if_neg hs, if_neg (by linarith : ¬ (0:ℝ) < s - (r - t))]
    exact Matrix.mulVec_zero _

set_option maxHeartbeats 200000 in
/-- Everything the input contributed up to any time in the step lies in the
enclosure computed for the whole step, once `U` contains the origin. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer [Mtimes IntervalMat S]
    {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by
  set A := toRealMat sys.A with hA
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  -- the delayed input is admissible: `u` where it reaches back into the step,
  -- the origin before that
  have hv_mem : ∀ τ ∈ Set.Ioc (0:ℝ) r, aux_delay u (r - t) (r - τ) ∈ construct U := by
    intro τ _
    simp only [aux_delay]
    split_ifs with h
    · have hrw : r - τ - (r - t) = t - τ := by ring
      rw [hrw]
      exact traj.input _ (by linarith)
    · exact h0
  -- measurable on each half of the step, exactly on the upper one and off only
  -- at `τ = t` on the lower
  have hv_meas : AEStronglyMeasurable (fun τ => aux_delay u (r - t) (r - τ))
      (volume.restrict (Set.Ioc 0 r)) := by
    have hsplit : Set.Ioc (0:ℝ) r = Set.Ioc 0 t ∪ Set.Ioc t r :=
      (Set.Ioc_union_Ioc_eq_Ioc ht0 htr).symm
    have hdisj : Disjoint (Set.Ioc (0:ℝ) t) (Set.Ioc t r) :=
      Set.disjoint_left.mpr fun _ hx hx' => absurd hx.2 (not_le.mpr hx'.1)
    rw [hsplit, Measure.restrict_union hdisj measurableSet_Ioc]
    refine AEStronglyMeasurable.add_measure ?_ ?_
    · have hne : ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0:ℝ) t)), τ ≠ t := by
        rw [ae_iff]
        simp
      refine (traj.aestronglyMeasurable_input_reflected (c := t) le_rfl).congr ?_
      filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with τ hτne hτmem
      have hlt : r - t < r - τ := by
        have : τ < t := lt_of_le_of_ne hτmem.2 hτne
        linarith
      simp only [aux_delay, if_pos hlt]
      have hrw : r - τ - (r - t) = t - τ := by ring
      rw [hrw]
    · refine (aestronglyMeasurable_const (b := (0 : Vec ℝ n))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτmem
      have hnlt : ¬ (r - t < r - τ) := not_lt.mpr (by linarith [hτmem.1])
      simp only [aux_delay, if_neg hnlt]
  -- the two integrals agree: shift by `r - t`, then drop the padded stretch
  have hcapped_int : IntervalIntegrable (aux_capped A u t) volume 0 t := by
    have hbase := traj.intervalIntegrable_input (le_refl (0:ℝ)) ht0 hbdd
    have hcomp : IntervalIntegrable
        (fun σ : ℝ => mulVecL (exp (t • A)) (exp ((-σ) • A) *ᵥ u σ)) volume 0 t :=
      ⟨(mulVecL (exp (t • A))).integrable_comp hbase.1,
       (mulVecL (exp (t • A))).integrable_comp hbase.2⟩
    refine hcomp.congr ?_
    intro σ hσ
    rw [Set.uIoc_of_le ht0] at hσ
    simp only [aux_capped, if_pos hσ.1]
    show exp (t • A) *ᵥ (exp ((-σ) • A) *ᵥ u σ) = _
    rw [Matrix.mulVec_mulVec, hmul]
    congr 2
  have hpad_int : IntervalIntegrable (aux_capped A u t) volume (t - r) 0 := by
    refine (intervalIntegrable_const (c := (0 : Vec ℝ n))).congr ?_
    intro σ hσ
    rw [Set.uIoc_of_le (by linarith : t - r ≤ (0:ℝ))] at hσ
    simp only [aux_capped, if_neg (not_lt.mpr hσ.2)]
  have hintegral : (∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ aux_delay u (r - t) s)
      = ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s := by
    have hshift : (∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ aux_delay u (r - t) s)
        = ∫ σ in (t - r)..t, aux_capped A u t σ := by
      have hpt : ∀ s : ℝ, exp ((r - s) • A) *ᵥ aux_delay u (r - t) s
          = aux_capped A u t (s - (r - t)) := fun s => aux_delay_integrand A u s
      simp only [hpt]
      have := intervalIntegral.integral_comp_sub_right (a := (0:ℝ)) (b := r)
        (aux_capped A u t) (r - t)
      simpa only [zero_sub, neg_sub, sub_sub_cancel] using this
    rw [hshift, ← intervalIntegral.integral_add_adjacent_intervals hpad_int hcapped_int]
    have hzero : (∫ σ in (t - r)..(0:ℝ), aux_capped A u t σ) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : Vec ℝ n)) ?_,
        intervalIntegral.integral_const]
      · simp
      · intro σ hσ
        have hσ0 : σ ≤ 0 := (Set.uIcc_of_le (by linarith : t - r ≤ (0:ℝ)) ▸ hσ).2
        simp only [aux_capped, if_neg (not_lt.mpr hσ0)]
    rw [hzero, zero_add]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with σ hσ
    have hpos : (0:ℝ) < σ := (Set.mem_uIoc.mp hσ).elim (fun h => h.1) (fun h => by linarith [h.2])
    simp only [aux_capped, if_pos hpos]
  have hkey := sys.inputSolution_outer hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd
    hv_mem hv_meas
  rwa [hintegral] at hkey

end CORALean.Real
