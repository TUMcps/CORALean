import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# A sum of interval matrices over an index range

`sumRangeFloat f k` is `f 0 + … + f (k - 1)`, one `Interval.matPlus` per term, each entry rounded
outward, from the origin: the interval counterpart of `∑ t ∈ range k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑ t < k, f t`, left to right. -/
def LinearARX.sumRangeFloat (f : ℕ → Interval (Mat 𝕋 m n)) : ℕ → Interval (Mat 𝕋 m n)
  | 0 => Interval.point fun _ _ => zero
  | k + 1 => Interval.matPlus (LinearARX.sumRangeFloat f k) (f k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
