import CORALean.ContSet.Interval.Real.Operations.Le

/-!
# `Interval.isequal`

CORA's `@interval/isequal` at two intervals: both bounds agree, which is containment both ways
(`Interval.le` each way). CORA compares up to a tolerance (default `eps`); this is the exact test,
tolerance zero. `Theorems/IsequalIff` says what it decides: equality of the denoted sets.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.isequal (I J : Interval α) : Prop := I.le J ∧ J.le I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
