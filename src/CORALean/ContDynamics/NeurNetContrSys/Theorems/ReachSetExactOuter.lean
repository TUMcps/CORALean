module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSetExact

@[expose] public section

/-!
# `reachSetExact` contains every sampled run

The cheap half, exactly as in the continuous classes: a run is in the set of
what runs reach by construction, so the proof is the pair itself. All the
content sits in the other half, `reachSetExact_subset_reach`.

## Inputs
* `sys` – closed-loop system
* `π` – controller function
* `H` – number of periods
* `R₀` – initial set
* `U_ext` – external input set
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal
* `t` – time

## Hypotheses
* `traj` – closed-loop trajectory

## Conclusion
* the run's state lies in the exact reachable set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSetExact_subset_reach`
to say what encloses it. -/
theorem NeurNetContrSys.IsTrajectory.reachSetExact_outer {sys : NeurNetContrSys P S n}
    {π : Vec ℝ n → Vec ℝ sys.m} {H : ℕ} {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {W : Set (Vec ℝ (nrOfDisturbances sys.plant))} {x : ℝ → Vec ℝ n}
    {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)}
    (traj : sys.IsTrajectory π H R₀ U_ext W x v w) (t : ℝ) :
    x t ∈ sys.reachSetExact π H R₀ U_ext W t :=
  ⟨x, v, w, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
