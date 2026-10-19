module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.reindexVars` over a floating-point scalar

The rows read at the variables `f`, as over ℝ, each with its slack: only the exponent matrix and
the box are reindexed, so nothing rounds (`mem_reindexVars_of_mem`).

## Inputs
* `P` – polynomial level set
* `n'` – new number of variables
* `f` – variable map

## Output
* the level set read at the variables `f`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows over `n'` variables, variable `k` being `P`'s variable `f k`, each with its slack. -/
def PolyLevelSet.reindexVars (P : PolyLevelSet 𝕋 n) {n' : ℕ} (f : Fin n' → Fin n) :
    PolyLevelSet 𝕋 n' where
  m := P.m
  q := P.q
  A := P.A
  R k l := P.R (f k) l
  b := P.b
  b_error := P.b_error
  op := P.op
  dom := P.dom.project f

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
