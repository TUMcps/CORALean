module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Basic

@[expose] public section

/-!
# The plant's input set of a closed loop

`U_nn × U_ext`: every input `[a; e]` with the network's part in `U_nn` and the external part in
`U_ext`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The plant's input set `U_nn × U_ext`. -/
def NeurNetContrSysDT.inputSet (sys : NeurNetContrSysDT P S n) (U_nn : Set (Vec ℝ sys.m))
    (U_ext : Set (Vec ℝ sys.nExt)) : Set (Vec ℝ (nrOfInputs sys.plant)) :=
  {u | ∃ a ∈ U_nn, ∃ e ∈ U_ext, u = sys.input a e}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
