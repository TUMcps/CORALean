module

public import CORALean.ContDynamics.NonlinearSys.Theorems.SubEqIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Confinement over a step, from a ball the field cannot cross

A run cannot leave a region faster than its field carries it: if `‖f‖ ≤ M` wherever the run is
confined, and the closed ball of radius `ρ > M(b - a)` about `x a` lies in `R`, then the run
stays in `R` for the whole of `[a, b]`. The classical a priori enclosure of validated
integration. The proof is the first-exit argument: below `τ = inf {t | x t ∉ R}` the run is
confined, so `‖x t - x a‖ ≤ M(b - a)`, which puts `x τ` in the interior of `R`. Strictness in
`hρ` buys the interior: at `ρ = M(b - a)` the run may reach the boundary exactly at `b`.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `R` – region
* `a` – start time
* `b` – end time
* `M` – field bound
* `ρ` – ball radius
* `y` – output trajectory

## Hypotheses
* `traj` – trajectory of the system
* `hab` – start before end
* `hT` – interval inside time set
* `hM₀` – bound nonnegative
* `hM` – field bounded on region
* `hρ` – radius exceeds travel distance
* `hball` – ball inside region

## Conclusion
* the trajectory stays in the region over the interval
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run whose field is bounded by `M` on `R` stays in `R` over `[a, b]` once a
ball of radius `ρ > M(b - a)` about `x a` lies in `R`. -/
theorem NonlinearSys.IsTrajectory.confined_of_ball {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {R : Set (Vec ℝ n)}
    {a b M ρ : ℝ} {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y) (hab : a ≤ b)
    (hT : Set.Icc a b ⊆ T)
    (hM₀ : 0 ≤ M) (hM : ∀ y ∈ R, ∀ v ∈ construct U, ‖sys.f y v‖ ≤ M)
    (hρ : M * (b - a) < ρ) (hball : Metric.closedBall (x a) ρ ⊆ R) : -- --- CONCL ---
    ∀ t ∈ Set.Icc a b, x t ∈ R := by -- --- PROOF ---
  intro t₁ ht₁
  by_contra ht₁R
  -- `τ`, the first time the run is outside `R`, exists as an infimum
  set B : Set ℝ := {t ∈ Set.Icc a b | x t ∉ R} with hB
  have hBne : B.Nonempty := ⟨t₁, ht₁, ht₁R⟩
  have hBbdd : BddBelow B := ⟨a, fun t ht => ht.1.1⟩
  set τ := sInf B with hτdef
  have haτ : a ≤ τ := le_csInf hBne fun t ht => ht.1.1
  have hτb : τ ≤ b := by
    obtain ⟨t, ht⟩ := hBne
    exact le_trans (csInf_le hBbdd ht) ht.1.2
  have hτIcc : τ ∈ Set.Icc a b := ⟨haτ, hτb⟩
  have hbelow : ∀ t ∈ Set.Ico a τ, x t ∈ R := by
    intro t ht
    by_contra h
    exact absurd (csInf_le hBbdd ⟨⟨ht.1, le_trans ht.2.le hτb⟩, h⟩) (not_le.2 ht.2)
  -- the field's integral on every closed interval below `τ`
  have hbound : ∀ t ∈ Set.Ico a τ, ‖x t - x a‖ ≤ M * (b - a) := by
    intro t ht
    have hsub : Set.Icc a t ⊆ Set.Ico a τ := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    have hsubT : Set.Icc a t ⊆ T := fun r hr =>
      hT ⟨hr.1, le_trans (le_trans hr.2 ht.2.le) hτb⟩
    have hbd : ∀ r ∈ Set.uIoc a t, ‖sys.f (x r) (u r)‖ ≤ M := by
      intro r hr
      rw [Set.uIoc_of_le ht.1] at hr
      exact hM _ (hbelow r (hsub ⟨hr.1.le, hr.2⟩)) _ (traj.input r (hsubT ⟨hr.1.le, hr.2⟩))
    have hmv := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [← traj.sub_eq_integral (hsubT (Set.left_mem_Icc.2 ht.1))
      (hsubT (Set.right_mem_Icc.2 ht.1)), abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - a)]
      at hmv
    exact hmv.trans (by nlinarith [ht.2, hτb, ht.1])
  -- the bound passes to `τ` itself, in the limit from below
  have hτball : x τ ∈ Metric.closedBall (x a) (M * (b - a)) := by
    rcases haτ.eq_or_lt with heq | hlt
    · rw [← heq]
      simpa using by positivity
    · have hne : (nhdsWithin τ (Set.Ico a τ)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (ne_of_lt hlt)]
        exact ⟨hlt.le, le_rfl⟩
      have htend : Filter.Tendsto x (nhdsWithin τ (Set.Ico a τ)) (nhds (x τ)) :=
        (traj.cont τ (hT hτIcc)).mono (fun r hr => hT ⟨hr.1, le_trans hr.2.le hτb⟩)
      refine Metric.isClosed_closedBall.mem_of_tendsto htend
        (eventually_mem_nhdsWithin.mono fun t ht => ?_)
      simpa [Metric.mem_closedBall, dist_eq_norm] using hbound t ht
  -- so `x τ` is interior to `R`, and continuity keeps the run in `R` just past `τ`
  have hnhds : R ∈ nhds (x τ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (by linarith : 0 < ρ - M * (b - a))) ?_
    intro y hy
    refine hball (Metric.mem_closedBall.2 ?_)
    have := dist_triangle y (x τ) (x a)
    have h1 := Metric.mem_ball.1 hy
    have h2 := Metric.mem_closedBall.1 hτball
    linarith
  -- some time of `B` sits inside every neighbourhood of `τ`, and this one is in `R`
  have hcont : ContinuousWithinAt x (Set.Icc a b) τ :=
    (traj.cont τ (hT hτIcc)).mono hT
  have hev : ∀ᶠ t in nhdsWithin τ (Set.Icc a b), x t ∈ R := hcont hnhds
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨V, hVopen, hτV, hVsub⟩ := hev
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hVopen τ hτV
  obtain ⟨t, htB, htlt⟩ := exists_lt_of_csInf_lt hBne (by linarith : τ < τ + δ)
  have hτt : τ ≤ t := csInf_le hBbdd htB
  have htV : t ∈ V := hδsub (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - τ)]
    linarith)
  exact htB.2 (hVsub ⟨htV, htB.1⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
