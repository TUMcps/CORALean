import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.lt`

CORA's `@interval/lt`: the strict version of `le`, both bounds of `I` strictly inside `J`'s in
every coordinate.
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

def Interval.lt (I J : Interval α) : Prop :=
  ∀ i, entry J.inf i < entry I.inf i ∧ entry I.sup i < entry J.sup i


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
