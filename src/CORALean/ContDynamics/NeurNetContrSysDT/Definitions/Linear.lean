module

public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# The loop at a linear plant, as a family

`NeurNetContrSysDT (LinearSysDT 𝕋 n) S n` over every state dimension `n`, bundled with its
external input set `U` (`U_ext`, CORA's `params.U` of the closed system), as `LinearSys.WithInput`
bundles its `U`; named, it is the family `Reach` is instantiated at: `Reach` takes a family
`ℕ → Type`, and a closed loop whose type is written `NeurNetContrSysDT.Linear 𝕋 S n` lets
`Reach.reach` find it, where the family `fun n => …` would have to be passed by hand.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The closed loop at a `LinearSysDT` plant, over every state dimension, with its external input
set. -/
structure NeurNetContrSysDT.Linear (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Type 1 where
  sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n
  U : S sys.nExt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
