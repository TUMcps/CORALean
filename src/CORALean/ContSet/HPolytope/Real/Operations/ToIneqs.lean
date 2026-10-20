module

public import CORALean.ContSet.HPolytope.Real.Operations.RowsRhs

@[expose] public section

/-!
# `HPolytope.toIneqs`

The same set with no equality rows: the inequalities, then each equality once each way, `rows`
over `rowsRhs`. What an operation reaches for when it must loosen every row alike, an equality
having no room to be loosened (`HPolytope.toIneqs_exact`).

## Inputs
* `P` – H-polytope

## Output
* every row of `P` as an inequality, each equality as its two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every row of `P` as an inequality, each equality as its two halves. -/
def HPolytope.toIneqs (P : HPolytope α) : HPolytope α where
  m := P.m + (P.me + P.me)
  A := P.rows
  b := P.rowsRhs
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
