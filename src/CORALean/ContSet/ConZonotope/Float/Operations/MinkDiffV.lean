module

public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# `ConZonotope.minkDiffV` over a floating-point scalar

[1, Prop. 6] on the stored floats: `Z ⊖ ⟨v⟩_V` for a zonotope `Z` and a polytope given by its
nonempty vertex list `v`, as the translated zonotopes `Z − vᵢ` intersected one at a time, the
way CORA's `@conZonotope/minkDiff`, method `'exact'`, folds. The translation is the float
`Zonotope.plus` with the point `−vᵢ` (negation is exact, the center's rounding goes into the
error box), and the intersection is the float `ConZonotope.intersection`, so the result is
outer, not exact.

## Inputs
* `k` – number of extra vertices
* `Z` – zonotope
* `v` – vertex list of the polytope

## Output
* the Minkowski difference of the zonotope and the polytope

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
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

/-- [1, Prop. 6]: `Z ⊖ ⟨v⟩_V`, the translated zonotopes `Z − v i` intersected in turn. -/
def ConZonotope.minkDiffV {k : ℕ} (Z : Zonotope (Vec 𝕋 n)) (v : Fin (k + 1) → Vec 𝕋 n) :
    ConZonotope 𝕋 (Vec 𝕋 n) :=
  let shifted : Fin (k + 1) → ConZonotope 𝕋 (Vec 𝕋 n) :=                 -- Z − v i
    fun i => (Z.plus (Zonotope.point (-(v i)))).conZonotope
  Fin.foldl k (fun cZ i => cZ.intersection (shifted i.succ)) (shifted 0)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
