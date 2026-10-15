module

public import CORALean.ContDynamics.Interfaces
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

The run is `IsTrajectory`, in its own file for it is stated with `input` and `inputSet`. With
`nExt = 0` (`ofFull`) the network drives every input.

## References

* [1] `contDynamics/@neurNetContrSys/neurNetContrSys.m`, `aux_computeProperties`
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
