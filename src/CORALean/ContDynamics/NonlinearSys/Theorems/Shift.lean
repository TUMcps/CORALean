module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

/-!
# A trajectory re-anchored at a later time

`IsTrajectory.init` pins the state at `0` and every guarantee in `LinearSys` is written from
`0`, so a method that takes a second step has to move the clock. This is the move:
`fun t => x (t₀ + t)` is a trajectory on any domain the shift carries into `T`, with the input
shifted alongside it. The field is time-invariant, so `flow` transports without a change of
vector field: the integral from `t₀` to `t₀ + t` is the difference of the two integral equations,
which is why `t₀ ∈ T` is asked. `R₀'` is a parameter and its membership a hypothesis: the state
reached at `t₀` is what the previous step enclosed, which makes this compose.

## Inputs
* `sys` – system
* `T` – time set
* `T'` – shifted time set
* `R₀` – initial set
* `R₀'` – set holding the later state
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `t₀` – anchor time

## Hypotheses
* `traj` – trajectory of the system
* `hT` – shift maps new set into old
* `ht₀` – anchor time in time set
* `h₀` – later state in the new initial set

## Conclusion
* the trajectory is a trajectory re-anchored at the later time
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory intervalIntegral

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `T` is a run on `T'` re-anchored at `t₀`, given a set holding
the state it starts from. -/
theorem NonlinearSys.IsTrajectory.shift {sys : NonlinearSys n m} {T T' : Set ℝ}
    {R₀ R₀' : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q} {t₀ : ℝ}
    (traj : sys.IsTrajectory T R₀ U x u y) (hT : Set.MapsTo (fun t => t₀ + t) T' T)
    (ht₀ : t₀ ∈ T) (h₀ : x t₀ ∈ construct R₀') :
    sys.IsTrajectory T' R₀' U (fun t => x (t₀ + t)) (fun t => u (t₀ + t))
      (fun t => y (t₀ + t)) where
  init := by simpa using h₀
  input t ht := traj.input _ (hT ht)
  meas := traj.meas.comp_quasiMeasurePreserving
    ((measurePreserving_add_left volume t₀).quasiMeasurePreserving.restrict hT)
  integrable t ht := by
    have h := ((traj.integrable t₀ ht₀).symm.trans (traj.integrable _ (hT ht))).comp_add_left t₀
    simpa using h
  cont := traj.cont.comp (continuousOn_const.add continuousOn_id) hT
  flow t ht := by
    have h1 := traj.flow _ (hT ht)
    have h2 := traj.flow t₀ ht₀
    simp only at h1
    rw [integral_comp_add_left (fun s => sys.f (x s) (u s)) t₀, add_zero,
      ← integral_interval_sub_left (traj.integrable _ (hT ht)) (traj.integrable t₀ ht₀)]
    rw [h1, h2]
    abel
  output t ht := traj.output _ (hT ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
