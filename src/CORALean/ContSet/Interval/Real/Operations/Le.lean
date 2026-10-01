import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.le`

CORA's `@interval/le`: `I ≤ J` holds when `J`'s lower bound is below `I`'s and `I`'s upper bound
is below `J`'s, in every coordinate. That is a containment test, `I ⊆ J`, not an order on the
points.
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

def Interval.le (I J : Interval α) : Prop :=
  ∀ i, entry J.inf i ≤ entry I.inf i ∧ entry I.sup i ≤ entry J.sup i


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
