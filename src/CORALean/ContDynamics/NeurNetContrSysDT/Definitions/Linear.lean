module

public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# The loop at a linear plant, as a family

`NeurNetContrSysDT (LinearSysDT 𝕋 n) S n` over every state dimension `n`, named, which is the
family `Reach` is instantiated at: `Reach` takes a family `ℕ → Type`, and a closed loop whose
type is written `NeurNetContrSysDT.Linear 𝕋 S n` lets `Reach.reach` find it, where the family
`fun n => …` would have to be passed by hand.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The closed loop at a `LinearSysDT` plant, over every state dimension. -/
abbrev NeurNetContrSysDT.Linear (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Type 1 :=
  NeurNetContrSysDT (LinearSysDT 𝕋 n) S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
