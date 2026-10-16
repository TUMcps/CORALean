module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LevelSet.isIntersecting_uniform` at float bounds

The float form of the real test of the same name: the bounds `(lb, ub)` of the interval
evaluation of each row at the box are stored floats, and the verdict is read off their signs by
`le` and `ltStrict`. Only `false` is certain: a row answers "disjoint" when its bound is
certified on the wrong side of the tolerance band (`tol < lb` for `≤`, `0 ≤ lb` for `<`, and for
`=` either `tol < lb` or `ub < -tol`); a row whose comparison is not certain counts as possibly
intersecting, which is what `true` says.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.isIntersecting_uniform (tol : 𝕋) (op : CORALean.Real.CompOp) (B : Fin m → Interval 𝕋) :
    Bool :=
  let lb : Fin m → 𝕋 := fun i => (B i).inf
  let ub : Fin m → 𝕋 := fun i => (B i).sup
  -- a row refutes a common point when its bound lies certainly outside the band
  let refutes : Fin m → Bool := fun i =>
    match op with
    | .eq => ltStrict tol (lb i) || ltStrict (ub i) (neg tol)
    | .le => ltStrict tol (lb i)
    | .lt => le zero (lb i)
  (List.finRange m).all fun i => !refutes i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
