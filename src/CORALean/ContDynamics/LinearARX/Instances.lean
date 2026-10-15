module

public import CORALean.ContDynamics.LinearARX.LinearARX
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `LinearARX` instantiates `ContDynamicsDT`

An ARX model has no state but its outputs, so the state is what CORA's `linearARX` takes it to
be, `p * dy` numbers: the window of the last `p` outputs. A run is a `IsTrajectory` of the
outputs, the state at step `k` the window `stack p y k` starting there; `du` inputs, no
disturbance.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- The ARX model as a `ContDynamicsDT` over its window of outputs. -/
instance LinearARX.contDynamicsDT : ContDynamicsDT (LinearARX 𝕋 dy du p) (p * dy) where
  nrOfInputs _ := du
  nrOfDisturbances _ := 0
  IsTrajectory sys X₀ U W x u w := ∃ y,
    LinearARX.IsTrajectory (S := 𝒮) sys X₀ U y u ∧
      (∀ k, x k = LinearARX.stack p y k) ∧ ∀ k, w k ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
