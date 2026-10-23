module

public import CORALean.NN.Operations.SmoothNetworkNu
public import CORALean.NN.Operations.SmoothNetworkOutputFn
public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# CORA's `neuralNetwork/nonlinearSysDT`: the system

CORA wraps the output function as
`nonlinearSysDT('nnSys', @(x,u) x, 1, dim_x, dim_u, f, dim_y, false)`: the state does not move and
`f` (`SmoothNetwork.outputFn`) is the output. The update is the identity on `n` states with
`SmoothNetwork.nu` inputs, and the output equation `g` of `NonlinearSysDT` is `outputFn`, with
`k` outputs.

## Inputs
* `n` – input width
* `k` – output width
* `N` – smooth network

## Output
* discrete-time system whose inputs perturb the biases
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system CORA returns: the state stays put, the inputs are the stacked bias perturbations
and the output is `outputFn`. Noncomputable because `outputFn` applies the real activations. -/
noncomputable def SmoothNetwork.toNonlinearSysDT {n k : ℕ} (N : SmoothNetwork n k) :
    NonlinearSysDT n N.nu where
  f x _ := x
  q := k
  g := N.outputFn
  dt := 1                                                           -- CORA passes `dt = 1`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
