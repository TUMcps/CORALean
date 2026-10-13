module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.representsa_origin`

CORA's `@interval/representsa_` at type `origin` with tolerance `0`: both bounds are zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.representsa_origin (I : Interval α) : Prop := I.inf = 0 ∧ I.sup = 0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
