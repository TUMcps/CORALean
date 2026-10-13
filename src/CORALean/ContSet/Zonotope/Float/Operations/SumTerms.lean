import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.Point

/-!
# A Minkowski sum of float zonotopes, term by term

`Real.Zonotope.sumTerms` at float zonotopes: `f 0 ⊕ … ⊕ f (m - 1)` from the point `0`, one
`plus` at a time, as the loops of [1] add their terms. Each partial sum is materialised, so a
long sum does not pay for its history on every read.

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_abstractionError`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f 0 ⊕ … ⊕ f (m - 1)`, `{0}` for `m = 0`. -/
def Zonotope.sumTerms (f : ℕ → Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Zonotope.point fun _ => zero
  | m + 1 => ((Zonotope.sumTerms f m).plus (f m)).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
