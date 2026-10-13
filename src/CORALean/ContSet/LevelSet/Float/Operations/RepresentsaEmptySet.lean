module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LevelSet.representsa_emptySet` at float bounds

The float form of the real test of the same name: the bounds `(lb, ub)` of each row's range
over the whole space are stored floats. A row is infeasible when `0 < lb` (for `≤` and `=`),
`ub < 0` (for `=`) or `0 ≤ lb` (for `<`) is certified by `ltStrict`, resp. `le`; every row must
be, as in the real test. Sufficient only: `true` proves the set empty, `false` says nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.representsa_emptySet (L : CORALean.Real.LevelSet n) (O : Fin L.m → 𝕋 × 𝕋) : Bool :=
  (List.finRange L.m).all fun i =>
    match L.op i with
    | .eq => ltStrict zero (O i).1 || ltStrict (O i).2 zero
    | .le => ltStrict zero (O i).1
    | .lt => le zero (O i).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
