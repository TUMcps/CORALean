module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic
public import CORALean.ContDynamics.NonlinDASys.Theorems.Basic
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A trajectory of the differential-algebraic system is one of the reduced system

`y_eq` puts `y t` at `h (x t) (u t)`, so `f` at the trajectory is the reduced field at it,
and the other fields are unchanged. The integral equation reads `f` on the whole window from
`0`, where `y_eq` holds only inside the time domain; on `[0, τ]` every such window is inside it.

## Inputs
* `sys` – system
* `red` – reduced model
* `τ` – horizon
* `R₀` – initial set
* `U` – input set
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal

## Hypotheses
* `traj` – DAE trajectory

## Conclusion
* the run is a trajectory of the reduced system
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.IsTrajectory.toNonlinearSys {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {τ : ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (Set.Icc 0 τ) R₀ U x y u z) :
    red.toNonlinearSys.IsTrajectory (Set.Icc 0 τ) R₀ U x u z := by -- --- PROOF ---
  have he : Set.EqOn (fun s => sys.f (x s) (y s) (u s)) (fun s => red.toNonlinearSys.f (x s) (u s))
      (Set.Icc 0 τ) := fun s hs => by
    show sys.f (x s) (y s) (u s) = sys.f (x s) (red.h (x s) (u s)) (u s)
    rw [traj.y_eq red hs]
  have hwin : ∀ t ∈ Set.Icc 0 τ, Set.uIcc 0 t ⊆ Set.Icc 0 τ := fun t ht =>
    Set.OrdConnected.uIcc_subset inferInstance (Set.left_mem_Icc.2 (ht.1.trans ht.2)) ht
  refine ⟨traj.init, traj.input, ?_, fun t ht => ?_, traj.cont, fun t ht => ?_, fun t ht => ?_⟩
  · exact traj.meas.congr (ae_restrict_of_forall_mem measurableSet_Icc he)
  · exact (intervalIntegrable_congr (he.mono (Set.uIoc_subset_uIcc.trans (hwin t ht)))).mp
      (traj.integrable t ht)
  · rw [traj.flow t ht, intervalIntegral.integral_congr (he.mono (hwin t ht))]
  · show z t = sys.h (x t) (red.h (x t) (u t)) (u t)
    rw [traj.output t ht, traj.y_eq red ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
