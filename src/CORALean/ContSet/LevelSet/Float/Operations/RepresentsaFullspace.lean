module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LevelSet.representsa_fullspace` at float bounds

The float form of the real test of the same name: the bounds `(lb, ub)` of each row's range
over the whole space are stored floats. A row holds everywhere when `ub ≤ 0` (for `≤`), `ub < 0`
(for `<`) or `lb = ub = 0` (for `=`, both comparisons both ways) is certified by `le`, resp.
`ltStrict`. Sufficient only: `true` proves the set is everything, `false` says nothing.

## Inputs
* `L` – level set
* `O` – float bounds of the rows over the whole space

## Output
* `true` only if every row certifiably holds everywhere
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.representsa_fullspace (L : CORALean.Real.LevelSet n) (O : Fin L.m → Interval 𝕋) :
    Bool :=
  (List.finRange L.m).all fun i =>
    match L.op i with
    | .eq => (le (O i).inf zero && le zero (O i).inf) && (le (O i).sup zero && le zero (O i).sup)
    | .le => le (O i).sup zero
    | .lt => ltStrict (O i).sup zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
