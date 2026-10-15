module

public import CORALean.DiscrDynamics.MarkovChain.Definitions.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `MarkovChain.stretch`

CORA's `stretch(Obj, factor)` on a chain whose `T` is one matrix (after `convertTransitionMatrix`):
`T` becomes `T^factor` and `OT` the average `OT (I + T + ⋯ + T^(factor-1)) / factor`, the chain
sampled `factor` times more coarsely. CORA's loops start at `2` and fail for `factor = 1`, where
`T_pow{i}` indexes an empty loop variable; the definition is the same expression there.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `stretch(Obj, factor)`: `T^factor`, and `OT` averaged over the intermediate steps. -/
noncomputable def MarkovChain.stretch {ι : Type} [Fintype ι] [DecidableEq ι]
    (Obj : MarkovChain.Stacked ι) (factor : ℕ) : MarkovChain.Stacked ι where
  T := Obj.T ^ factor
  OT := (1 / (factor : ℝ)) • (Obj.OT * ∑ k ∈ Finset.range factor, Obj.T ^ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
