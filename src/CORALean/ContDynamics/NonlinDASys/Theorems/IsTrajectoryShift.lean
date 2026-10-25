module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

/-!
# A run of the DAE, restarted at a later time

A run of the DAE on `[0, T]` is, from `a` on, a run on `[0, b]` for `a + b ≤ T` once time is
counted from `a`, started in any set that holds `x(a)`. What `[1, Alg. 1]` does at each step:
the set `Rᵈ(t_k)` is the new initial set, and the step's soundness is about the run from `t_k`.

## Inputs
* `sys` – system
* `T` – horizon
* `R₀` – initial zonotope
* `U` – input zonotope
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal
* `a` – restart time
* `b` – new horizon
* `Z` – new initial set

## Hypotheses
* `traj` – DAE trajectory
* `ha` – restart time nonnegative
* `hab` – the new window fits in the horizon
* `hx` – the state at the restart lies in `Z`

## Conclusion
* the shifted run is a trajectory from the new set

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet MeasureTheory

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run from `a` on, with time counted from `a`, is a run on `[0, b]` from any set holding
`x(a)`. -/
theorem NonlinDASys.IsTrajectory.shift {sys : NonlinDASys n p m} {T : ℝ} {R₀ : Zonotope (Vec ℝ n)}
    {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    {z : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 T) R₀ U x y u z) {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a + b ≤ T) {Z : Zonotope (Vec ℝ n)} (hx : x a ∈ Z.construct) :
    sys.IsTrajectory (S := 𝒵) (Set.Icc 0 b) Z U (fun s => x (a + s)) (fun s => y (a + s))
      (fun s => u (a + s)) (fun s => z (a + s)) where
  init := by
    show x (a + 0) ∈ Z.construct
    rw [add_zero]
    exact hx
  input s hs := traj.input (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  meas := traj.meas.comp_quasiMeasurePreserving
    ((measurePreserving_add_left volume a).quasiMeasurePreserving.restrict
      fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  integrable s hs := by
    have haT : a ∈ Set.Icc 0 T := ⟨ha, by linarith [hs.1, hs.2]⟩
    have hmem : a + s ∈ Set.Icc 0 T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa using ((traj.integrable a haT).symm.trans (traj.integrable _ hmem)).comp_add_left a
  cont := traj.cont.comp ((continuousOn_const (c := a)).add continuousOn_id)
    fun s (hs : s ∈ Set.Icc 0 b) => show a + s ∈ Set.Icc 0 T from
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
  flow s hs := by
    -- the integral from `a` to `a + s`, the difference of the equations at the two ends
    have haT : a ∈ Set.Icc 0 T := ⟨ha, by linarith [hs.1, hs.2]⟩
    have hmem : a + s ∈ Set.Icc 0 T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := traj.flow (a + s) hmem
    have h2 := traj.flow a haT
    show x (a + s) = x (a + 0) + ∫ r in (0:ℝ)..s, sys.f (x (a + r)) (y (a + r)) (u (a + r))
    rw [intervalIntegral.integral_comp_add_left (fun r => sys.f (x r) (y r) (u r)) a, add_zero,
      ← intervalIntegral.integral_interval_sub_left (traj.integrable _ hmem)
        (traj.integrable a haT), h1, h2]
    abel
  constraint s hs := traj.constraint (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  output s hs := traj.output (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
