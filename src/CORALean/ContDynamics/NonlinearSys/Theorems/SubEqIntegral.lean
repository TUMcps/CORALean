module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# What a run moves between two times is the integral of its field

The integral equation is anchored at `0`; subtracting it at `a` from it at `b` leaves the
integral from `a` to `b`, the field integrable on both pieces. This is the form every estimate
over a window `[a, b]` reads, where a classical run read the mean value inequality.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `a` – first time
* `b` – second time

## Hypotheses
* `traj` – trajectory of the system
* `ha` – first time in time set
* `hb` – second time in time set

## Conclusion
* the state change equals the field integral between the times
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet intervalIntegral

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x b - x a` is the field's integral from `a` to `b`, for `a b ∈ T`. -/
theorem NonlinearSys.IsTrajectory.sub_eq_integral {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T R₀ U x u y) {a b : ℝ} (ha : a ∈ T) (hb : b ∈ T) :
    x b - x a = ∫ s in a..b, sys.f (x s) (u s) := by
  rw [← integral_interval_sub_left (traj.integrable b hb) (traj.integrable a ha),
    traj.flow b hb, traj.flow a ha]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
