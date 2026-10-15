module

public import CORALean.ContDynamics.LinearSys.Instances
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The loop at a linear plant, as a family

`NeurNetContrSys (LinearSys 𝕋 n) S n` over every state dimension `n`, bundled with its external
input set `U` (`U_ext`, CORA's `params.U` of the closed system), as `LinearSys.WithInput` bundles
its `U`; named, it is the family `Reach` is instantiated at, as `NeurNetContrSysDT.Linear` is. The
control period `dt` is the system's own; the plant's step `Δt` stays in `options`, which CORA
checks divides `dt`, and so does `reach`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The closed loop at a `LinearSys` plant, over every state dimension, with its external input
set. -/
structure NeurNetContrSys.Linear (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Type 1 where
  sys : NeurNetContrSys (LinearSys 𝕋 n) S n
  U : S sys.nExt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
