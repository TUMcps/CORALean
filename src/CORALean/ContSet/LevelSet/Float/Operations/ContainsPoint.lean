import CORALean.ContSet.LevelSet.Real.LevelSet
import CORALean.ContSet.Interval.Float.Interval

/-!
# `LevelSet.containsPoint` at float bounds

CORA's `@levelSet/contains_` for a point evaluates `funHan` there; the real function has no
machine form, so its value at the point enters as stored float bounds `(lo, hi)` per row (an
interval evaluation, an argument assumed to enclose the value), and each row's comparison with
`0` is certified: `hi ≤ 0` by `le` for `≤`, `hi < 0` by `ltStrict` for `<`, and `lo = hi = 0`
(`le` both ways) for `=`. Only `true` is certain.
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

def LevelSet.containsPoint (L : CORALean.Real.LevelSet n) (B : Fin L.m → 𝕋 × 𝕋) : Bool :=
  (List.finRange L.m).all fun i =>
    match L.op i with
    | .le => le (B i).2 zero
    | .lt => ltStrict (B i).2 zero
    | .eq => (le (B i).1 zero && le zero (B i).1) && (le (B i).2 zero && le zero (B i).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
