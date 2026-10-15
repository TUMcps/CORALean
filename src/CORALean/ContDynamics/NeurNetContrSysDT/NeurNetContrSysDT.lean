module

public import CORALean.ContDynamics.Interfaces
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a discrete-time plant: the representation

CORA's `neurNetContrSys` at a discrete-time plant [1], any `ContDynamicsDT` — CORA accepts
`linearSysDT` and `nonlinearSysDT`, here also `LinParamSysDT` and the ARX models: the
controller reads the state and produces the plant's input, `u(k) = π(x(k))`, and the plant
advances by its own equation. One controller invocation per plant step, so there is no
inter-sample behaviour to describe; `NeurNetContrSys` is the continuous-time loop. The network
drives every input of the plant; CORA's further external inputs (`n_ext`, the inputs past the
network's outputs) are not modelled. The plant's disturbance is the loop's: CORA's closed loop
at a `linearSysDT` drops `E`, so what is proved of its reachability there is for a disturbance
`E` sends to `0`.

`Trajectory` is a run of the plant whose input is the controller's output at the state it
reads, with no input set and no free input. At a `LinearSysDT` with no disturbance a run is the
orbit of `map` from a point of `R₀` (`Trajectory.linear`), which `Theorems.TrajectoryIterate`
states rather than leaves implied.

## References

* [1] `contDynamics/@neurNetContrSys/neurNetContrSys.m`, `aux_computeProperties`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling it, which drives every input of the plant. -/
structure NeurNetContrSysDT (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamicsDT P n] where
  plant : P
  contr : NeuralNetwork S n (nrOfInputs plant)

/-- One admissible run: a run of the plant from `R₀` whose input at every step is `π` of the
state, its disturbance in `W`. `π` is what the controller computes, which `NeuralNetwork` does
not store — `contr.Sound π` is what ties it back. -/
def NeurNetContrSysDT.Trajectory (sys : NeurNetContrSysDT P S n)
    (π : Vec ℝ n → Vec ℝ (nrOfInputs sys.plant)) (R₀ : S n)
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (x : ℕ → Vec ℝ n)
    (w : ℕ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop :=
  ContDynamicsDT.Trajectory sys.plant (construct R₀) Set.univ W x (fun k => π (x k)) w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
