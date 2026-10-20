module

public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf

@[expose] public section

/-!
# `HPolytope.minkDiffOf`'s counts

Every row survives, inequalities and equalities alike — `minkDiffOf` only shifts
`b`, never adds or drops a row. `rfl` against the structure instance in
`Operations/MinkDiffOf.lean`.

## Inputs
* `P` – H-polytope
* `T` – set of points

## Hypotheses
* `u` – a support bound of `T` along each row

## Conclusion
* `minkDiffOf` keeps the number of inequalities of `P`
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `m` count of `minkDiffOf`'s result. -/
theorem HPolytope.minkDiffOf_m (P : HPolytope α) (T : Set α) (u : ∀ i, SupportBound T (P.A i)) :
    (P.minkDiffOf T u).m = P.m := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
