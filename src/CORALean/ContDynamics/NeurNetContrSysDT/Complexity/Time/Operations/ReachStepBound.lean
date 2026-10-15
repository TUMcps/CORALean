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
`mtimes`, `hEnc` a bound on what the controller's enclosure and `hU` on what the external inputs
carry into the `reduce`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same costs at a step's worst case: `o * n` generators reaching the
`mtimes`, `hEnc` a bound on what the controller's enclosure and `hU` on what the external inputs
carry into the `reduce`. -/
def NeurNetContrSysDT.reachStepBound (sys : NeurNetContrSysDT (LinearSysDT ℝ n) 𝒵 n)
    (o hEnc hU : ℕ) (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost) : Cost :=
  NeuralNetwork.encloseCost LC sys.contr
    + (Zonotope.mtimesCost n sys.m hEnc + Zonotope.plusCost n)
    + (Zonotope.mtimesCost n sys.nExt hU + Zonotope.plusCost n)
    + LinearSysDT.reachStepBound n (hEnc + hU) o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
