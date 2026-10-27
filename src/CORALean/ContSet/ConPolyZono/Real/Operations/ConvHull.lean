module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Real.Operations.LinComb

@[expose] public section

/-!
# `ConPolyZono.convHull`

CORA's `@conPolyZono/convHull_`, and [1, Prop. 9]: the convex hull of two
constrained polynomial zonotopes, as `n + 1` weighted copies of their linear
combination. [1] substitutes the combination for the union inside its
Carathéodory definition of the hull, which costs fewer factors than the union of
[1, Thm. 1] would; the two have the same hull because the union sits inside the
combination and the combination inside the hull.

Pinned to `Vec`, since the count of copies is the ambient dimension plus one.

## Inputs
* `n` – ambient dimension
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* convex hull as weighted copies

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The convex hull, as `n + 1` weighted copies of the linear combination. -/
noncomputable def ConPolyZono.convHull {n : ℕ} (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) :=
  ConPolyZono.convHullSingle (n + 1) (cPZ₁.linComb cPZ₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
