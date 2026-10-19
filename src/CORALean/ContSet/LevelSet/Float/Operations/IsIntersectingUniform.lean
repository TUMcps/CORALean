module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LevelSet.isIntersecting_uniform` at float bounds

The float form of the real test of the same name (the level set first, its operators read from
it): the bounds `(lb, ub)` of the interval evaluation of each row at the box are stored floats,
and the verdict is read off their signs by `le` and `ltStrict`. Only `false` is certain: a row
answers "disjoint" when its bound is certified on the wrong side of the tolerance band (`tol < lb`
for `≤`, `0 ≤ lb` for `<`, and for `=` either `tol < lb` or `ub < -tol`); a row whose comparison
is not certain counts as possibly intersecting, which is what `true` says.

## Inputs
* `n` – dimension
* `ls` – level set
* `tol` – tolerance
* `B` – float bounds of the rows over the box

## Output
* `false` only if some row certifiably refutes a common point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isIntersecting_uniform {n : ℕ} (ls : CORALean.Real.LevelSet n) (tol : 𝕋)
    (B : Fin ls.m → Interval 𝕋) : Bool :=
  let lb : Fin ls.m → 𝕋 := fun i => (B i).inf
  let ub : Fin ls.m → 𝕋 := fun i => (B i).sup
  -- a row refutes a common point when its bound lies certainly outside the band
  let refutes : Fin ls.m → Bool := fun i =>
    match ls.op i with
    | .eq => ltStrict tol (lb i) || ltStrict (ub i) (neg tol)
    | .le => ltStrict tol (lb i)
    | .lt => le zero (lb i)
  (List.finRange ls.m).all fun i => !refutes i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
