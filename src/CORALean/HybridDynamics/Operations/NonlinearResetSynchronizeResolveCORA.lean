import CORALean.HybridDynamics.Operations.NonlinearResetSynchronize
import CORALean.HybridDynamics.Operations.NonlinearResetResolveCORA

/-!
# `NonlinearReset.synchronizeResolveCORA`

The reset of `transition/synchronize` for nonlinear resets as CORA computes it: the lifted resets
are combined by `synchronize(resets, idStates)` and the result goes through CORA's `resolve`,
`reset = resolve(reset_sync, flowList, stateBinds, inputBinds)`, with `inputBinds` the binds of
the parallel automaton (`mergeTransitionSets.m` passes `pHA.bindsInputs`). Only this reset step
is modelled, not the guard, the target or the conversion of linear resets.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k q : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.synchronizeResolveCORA (rs : Fin q → NonlinearReset N (∑ i, m i) N)
    (idStates : Finset (Fin N)) (out : ∀ i, Vec ℝ (n i) → Vec ℝ (m i) → Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    NonlinearReset N (NonlinearReset.globalColumns inputBinds) N :=
  -- `reset_sync = synchronize(resets, idStates)`
  let reset_sync := NonlinearReset.synchronize rs idStates
  -- `reset = resolve(reset_sync, flowList, stateBinds, inputBinds)`
  reset_sync.resolveCORA out stateBinds inputBinds

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
