import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb

/-!
# `ConPolyZono.convHull`

CORA's `@conPolyZono/convHull_`, [1, Prop. 9]: the convex hull of two constrained
polynomial zonotopes, as `n + 1` weighted copies of their linear combination. Pinned to `Vec`, the
count of copies being the ambient dimension plus one.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex hull, as `n + 1` weighted copies of the linear combination. -/
def ConPolyZono.convHull (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  ConPolyZono.convHullSingle (n + 1) (cPZ₁.linComb cPZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
