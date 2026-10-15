module

public import CORALean.ContDynamics.Interfaces
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a discrete-time plant: the representation

CORA's `neurNetContrSys` at a discrete-time plant [1], any `ContDynamicsDT` — CORA accepts
`linearSysDT` and `nonlinearSysDT`, here also `LinParamSysDT` and the ARX models: the
controller reads the state and produces the first `m` inputs of the plant, `u_nn(k) = π(x(k))`,
and the plant advances by its own equation. The remaining `nExt = nrOfInputs − m` inputs are
external, CORA's `n_ext`, in `U_ext` (CORA's `params.U`); the plant receives `U_nn × U_ext`
(`inputSet`), its input vector being `[a; e]` (`input`), as in `NeurNetContrSys`, the
continuous-time loop. One controller invocation per plant step, so a run is indexed by the step
`k`, at time `k dt` for the sampling time `dt` the system stores. The plant's disturbance is the
loop's: CORA's closed loop at a `linearSysDT` drops `E`, so what is proved of its reachability
there is for a disturbance `E` sends to `0`.

`Trajectory` is a run of the plant whose input at every step is the controller's output at the
state it reads together with an external input `v k` in `U_ext`; `U_nn` is all of the network's
outputs, the one a step takes being fixed by the controller. At a `LinearSysDT` a run steps by
`map` (`Trajectory.linear`). With `nExt = 0` (`ofFull`) the network drives every input.

## References

* [1] `contDynamics/@neurNetContrSys/neurNetContrSys.m`, `aux_computeProperties`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling its first `m` inputs, the rest external, and the
sampling time `dt`: CORA's `neurNetContrSys(sys, nn, dt)`. -/
structure NeurNetContrSysDT (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamicsDT P n] where
  plant : P
  m : ℕ
  hm : m ≤ nrOfInputs plant
  contr : NeuralNetwork S n m
  dt : ℝ

/-- CORA's `n_ext`: the plant's inputs the network does not drive. -/
abbrev NeurNetContrSysDT.nExt (sys : NeurNetContrSysDT P S n) : ℕ := nrOfInputs sys.plant - sys.m

/-- The plant's input `[a; e]`: the network's output `a`, the external input `e`. -/
def NeurNetContrSysDT.input (sys : NeurNetContrSysDT P S n) (a : Vec ℝ sys.m)
    (e : Vec ℝ sys.nExt) : Vec ℝ (nrOfInputs sys.plant) :=
  joinInput sys.hm a e

/-- The plant's input set `U_nn × U_ext`. -/
def NeurNetContrSysDT.inputSet (sys : NeurNetContrSysDT P S n) (U_nn : Set (Vec ℝ sys.m))
    (U_ext : Set (Vec ℝ sys.nExt)) : Set (Vec ℝ (nrOfInputs sys.plant)) :=
  {u | ∃ a ∈ U_nn, ∃ e ∈ U_ext, u = sys.input a e}

/-- The loop in which the network drives every input (`m = nrOfInputs`, no external input). -/
def NeurNetContrSysDT.ofFull (plant : P) (contr : NeuralNetwork S n (nrOfInputs plant))
    (dt : ℝ) : NeurNetContrSysDT P S n :=
  ⟨plant, nrOfInputs plant, le_rfl, contr, dt⟩

/-- One admissible run from `R₀`: at every step the plant's input is `π` of the state with the
external input `v k` in `U_ext`, its disturbance in `W`. -/
def NeurNetContrSysDT.Trajectory (sys : NeurNetContrSysDT P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (R₀ : S n) (U_ext : Set (Vec ℝ sys.nExt))
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (x : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ sys.nExt) (w : ℕ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop :=
  ContDynamicsDT.Trajectory sys.plant (construct R₀) (sys.inputSet Set.univ U_ext) W x
    (fun k => sys.input (π (x k)) (v k)) w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
