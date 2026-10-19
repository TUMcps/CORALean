module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.reindexVars`

The rows read at the variables `f`: variable `k` of the result is variable `f k` of `P`, its
exponents copied, and the coefficients, right-hand sides and operators stand. Where `f` is
injective and reaches every variable a monomial reads, the rows at `y ∘ f` are `P`'s at `y`
(`eval_reindexVars`), which is how a constrained polynomial zonotope drops the factors no
monomial reads (`ConPolyZono.compactFactors`). CORA's `@levelSet/lift_` read the other way.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows over `n'` variables, variable `k` being `P`'s variable `f k`. -/
def PolyLevelSet.reindexVars (P : PolyLevelSet n) {n' : ℕ} (f : Fin n' → Fin n) :
    PolyLevelSet n' where
  m := P.m
  q := P.q
  A := P.A
  R k l := P.R (f k) l
  b := P.b
  op := P.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
