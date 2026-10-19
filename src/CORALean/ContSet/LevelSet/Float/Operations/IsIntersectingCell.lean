module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LevelSet.isIntersecting_cell` at float bounds

The float form of the real test of the same name, the branch with one operator per row (CORA's
cell of operators). As in CORA every operator but `≤` is read as `lb < 0`, so the theorem needs
the level set free of `=` rows (see the real test's counterexample). Only `false` is certain: a
row refutes a common point when `tol < lb` (for `≤`) or `0 ≤ lb` (otherwise) is certified by
`ltStrict`, resp. `le`.

## Inputs
* `tol` – tolerance
* `op` – comparison operator per row
* `B` – float bounds of the rows over the box

## Output
* `false` only if some row certifiably refutes a common point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isIntersecting_cell (tol : 𝕋) (op : Fin m → CORALean.Real.CompOp)
    (B : Fin m → Interval 𝕋) : Bool :=
  let lb : Fin m → 𝕋 := fun i => (B i).inf
  -- a row refutes a common point when its lower bound lies certainly outside the band
  let refutes : Fin m → Bool := fun i =>
    match op i with
    | .le => ltStrict tol (lb i)
    | _ => le zero (lb i)
  (List.finRange m).all fun i => !refutes i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
