module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.InputSet

@[expose] public section

/-!
# A run of the closed loop

A run of the plant whose input at every step is the controller's output at the state it reads
together with an external input `v k` in `U_ext`; `U_nn` is all of the network's outputs, the one a
step takes being fixed by the controller. Stated with the plant's `input` and `inputSet`, which is
why it is not in the file of `NeurNetContrSysDT`. At a `LinearSysDT` a run steps by `map`
(`IsTrajectory.linear`).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One admissible run from `R₀`: at every step the plant's input is `π` of the state with the
external input `v k` in `U_ext`, its disturbance in `W`. -/
def NeurNetContrSysDT.IsTrajectory (sys : NeurNetContrSysDT P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (R₀ : S n) (U_ext : Set (Vec ℝ sys.nExt))
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (x : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ sys.nExt) (w : ℕ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop :=
  ContDynamicsDT.IsTrajectory sys.plant (construct R₀) (sys.inputSet Set.univ U_ext) W x
    (fun k => sys.input (π (x k)) (v k)) w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
