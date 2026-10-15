module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.InputSet

@[expose] public section

/-!
# A run of the closed loop

The full run over `H` periods, each a run of the plant on `[0, dt]` shifted to the period's start:
at a sampling instant `u` jumps, and a run is a run of the plant only within a period. Stated with
the plant's `input` and `inputSet`, which is why it is not in the file of `NeurNetContrSys`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The full run over `H` control periods of length `sys.dt` from `R₀`: on period `i`, a run of
the plant under the held `π(x(i dt))`, an external input `v` in `U_ext` and a disturbance in `W`. -/
structure NeurNetContrSys.IsTrajectory (sys : NeurNetContrSys P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (H : ℕ) (R₀ : S n)
    (U_ext : Set (Vec ℝ sys.nExt)) (W : Set (Vec ℝ (nrOfDisturbances sys.plant)))
    (x : ℝ → Vec ℝ n) (v : ℝ → Vec ℝ sys.nExt)
    (w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop where
  init : x 0 ∈ construct R₀
  flow (i : ℕ) (hi : i < H) :
    ContDynamics.IsTrajectory sys.plant (Set.Icc 0 sys.dt) Set.univ
      (sys.inputSet {π (x ((i : ℝ) * sys.dt))} U_ext) W
      (fun t => x ((i : ℝ) * sys.dt + t))
      (fun t => sys.input (π (x ((i : ℝ) * sys.dt))) (v ((i : ℝ) * sys.dt + t)))
      (fun t => w ((i : ℝ) * sys.dt + t))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
