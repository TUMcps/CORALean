module

public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic

@[expose] public section

/-!
# `ContDynamics/NeurNetContrSysDT/Operations`: small declarations

The plant's input `[a; e]` of a closed loop and the loop in which the network drives every input.

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

section
open ContSet ContDynamicsDT
variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ================================  `NeurNetContrSysDT.input`  ================================= --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- The plant's input `[a; e]`: the network's output `a`, the external input `e`. -/
def NeurNetContrSysDT.input (sys : NeurNetContrSysDT P S n) (a : Vec ℝ sys.m)
    (e : Vec ℝ sys.nExt) : Vec ℝ (nrOfInputs sys.plant) :=
  joinInput sys.hm a e


-- ================================  `NeurNetContrSysDT.ofFull`  ================================ --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- The loop in which the network drives every input (`m = nrOfInputs`, no external input). -/
def NeurNetContrSysDT.ofFull (plant : P) (contr : NeuralNetwork S n (nrOfInputs plant))
    (dt : ℝ) : NeurNetContrSysDT P S n :=
  ⟨plant, nrOfInputs plant, le_rfl, contr, dt⟩

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
