module

public import CORALean.NN.Operations.SmoothNetworkNu
public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# CORA's `neuralNetwork/nonlinearSysDT`: the system

CORA wraps the output function as
`nonlinearSysDT('nnSys', @(x,u) x, 1, dim_x, dim_u, f, dim_y, false)`: the state does not move and
`f` (`SmoothNetwork.outputFn`) is the output. `NonlinearSysDT` carries only the update map, so the
system is the identity update on `n` states with `SmoothNetwork.nu` inputs.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system CORA returns: the state stays put, the inputs are the stacked bias perturbations. -/
def SmoothNetwork.toNonlinearSysDT {n k : ℕ} (N : SmoothNetwork n k) : NonlinearSysDT n N.nu where
  f x _ := x
  q := n
  g x _ := x
  dt := 1                                                           -- CORA passes `dt = 1`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
