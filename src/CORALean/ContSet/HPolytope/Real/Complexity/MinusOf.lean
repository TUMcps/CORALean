import CORALean.ContSet.HPolytope.Real.Operations.MinusOf

/-!
# `HPolytope.minusOf`'s counts

Every row survives, inequalities and equalities alike — `minusOf` only shifts
`b`, never adds or drops a row. `rfl` against the structure instance in
`Operations/MinusOf.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minusOf_m (P : HPolytope α) (T : Set α) (u : ∀ i, SupportBound T (P.A i)) :
    (P.minusOf T u).m = P.m := rfl

theorem HPolytope.minusOf_me (P : HPolytope α) (T : Set α) (u : ∀ i, SupportBound T (P.A i)) :
    (P.minusOf T u).me = P.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
