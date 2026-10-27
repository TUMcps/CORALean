module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb

@[expose] public section

/-!
# `ConPolyZono.convHull`

CORA's `@conPolyZono/convHull_`, [1, Prop. 9]: the convex hull of two constrained
polynomial zonotopes, as `n + 1` weighted copies of their linear combination. Pinned to `Vec`, the
count of copies being the ambient dimension plus one.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* convex hull enclosure

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
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

/-- The convex hull, as `n + 1` weighted copies of the linear combination. -/
def ConPolyZono.convHull (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  ConPolyZono.convHullSingle (n + 1) (cPZ₁.linComb cPZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
