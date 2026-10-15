module

public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.Basic
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.NN.Complexity.Time.Operations.EncloseCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `NeurNetContrSysDT.reachStepBound`

The same costs at a step's worst case: `o * n` generators reaching the
`mtimes`, and `hEnc` a bound on what the controller's enclosure carries into
the `reduce`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same costs at a step's worst case: `o * n` generators reaching the
`mtimes`, and `hEnc` a bound on what the controller's enclosure carries into
the `reduce`. -/
def NeurNetContrSysDT.reachStepBound (sys : NeurNetContrSysDT ℝ 𝒵 n) (o hEnc : ℕ)
    (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost) : Cost :=
  NeuralNetwork.encloseCost LC sys.contr
    + (Zonotope.mtimesCost n sys.plant.m hEnc + Zonotope.plusCost n)
    + LinearSysDT.reachStepBound n hEnc o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
