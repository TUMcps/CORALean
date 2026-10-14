module

public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A sum of float interval matrices, term by term

`f 0 + … + f (m − 1)` of interval matrices, from the point `0`, one `matPlus` at a time, each
partial sum materialised: the series of [1] summed as their loops add their terms.

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_constantFlow`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f 0 + … + f (k − 1)`, the point `0` for `k = 0`. -/
def Interval.sumTermsMat (f : ℕ → Interval (Mat 𝕋 m n)) : ℕ → Interval (Mat 𝕋 m n)
  | 0 => Interval.point fun _ _ => zero
  | k + 1 => (Interval.matPlus (Interval.sumTermsMat f k) (f k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
