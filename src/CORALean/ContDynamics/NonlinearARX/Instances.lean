module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NonlinearARX` instantiates `ContDynamicsDT`

An ARX model has no state but its outputs, so the state is what CORA's `nonlinearARX` takes it
to be, `p * dy` numbers: the window of the last `p` outputs. A run is a `IsTrajectory` of the
outputs, the state at step `k` the window `stack p y k` starting there; `du` inputs, no
disturbance.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- The ARX model as a `ContDynamicsDT` over its window of outputs. -/
instance NonlinearARX.contDynamicsDT : ContDynamicsDT (NonlinearARX dy du p) (p * dy) where
  nrOfInputs _ := du
  nrOfDisturbances _ := 0
  IsTrajectory sys X₀ U W x u w := ∃ y,
    NonlinearARX.IsTrajectory (S := 𝒮) sys X₀ U y u ∧
      (∀ k, x k = NonlinearARX.stack p y k) ∧ ∀ k, w k ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
