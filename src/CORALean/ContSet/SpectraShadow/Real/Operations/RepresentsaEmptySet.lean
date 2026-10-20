module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.representsa_emptySet`

CORA's `@spectraShadow/representsa_` at type `emptySet`: `~aux_feasible`, the linear matrix
inequality has no solution.

## Inputs
* `S` – spectrahedral shadow

## Output
* `aux_feasible` negated: the linear matrix inequality has no solution
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_feasible` negated: the linear matrix inequality has no solution. -/
def SpectraShadow.representsa_emptySet (S : SpectraShadow α) : Prop :=
  ¬ ∃ β : Fin S.m → ℝ, (S.A₀ + ∑ i, β i • S.A i).PosSemidef

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
