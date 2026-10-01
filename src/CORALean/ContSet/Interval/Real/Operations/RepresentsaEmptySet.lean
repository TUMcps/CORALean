import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# `Interval.representsa_emptySet`

CORA's `@interval/representsa_` at type `emptySet`: the interval denotes the empty set. In CORA
that is a zero-size `inf`; here the crossed bounds, which is what `Interval.empty` returns.
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

def Interval.representsa_emptySet (I : Interval α) : Prop := ¬I.IsNonempty


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
