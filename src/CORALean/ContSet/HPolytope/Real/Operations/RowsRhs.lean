module

public import CORALean.ContSet.HPolytope.Real.Operations.Rows

@[expose] public section

/-!
# `HPolytope.rowsRhs`

The right-hand sides of `HPolytope.rows`: `b`, then `be`, then `-be`. A point lies in the
polytope exactly when every row, with its right-hand side, holds (`mem_construct_iff_rows`): an
equality is the pair of opposite inequalities.

## Inputs
* `P` – H-polytope

## Output
* the right-hand side of each row of `rows`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand side of each row of `rows`. -/
def HPolytope.rowsRhs (P : HPolytope α) : Fin (P.m + (P.me + P.me)) → ℝ :=
  Fin.append P.b (Fin.append P.be fun i => -P.be i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
