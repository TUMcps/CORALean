module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Shift

@[expose] public section

/-!
# `ConZonotope.minkDiffV`

[1, Prop. 6]'s constrained-zonotope formula for `Z ⊖ P`, `Z` a zonotope and `P` a polytope given
by its (nonempty) vertex list `v : Fin (k+1) → Vec ℝ n`: intersect the translated zonotopes
`Z − v 0, Z − v 1, ...` one at a time, which is `⋂ᵢ (Z − vᵢ)` computed the way
`ConZonotope.intersection` is the only exact intersection this development has. CORA's
`@conZonotope/minkDiff`, `'exact'` method, folds the very same way.

Not stated against the block matrix `[1]` prints: `ConZonotope.P` is an `HPolytope`, not a bare
equality system, so assembling `[1]`'s `A` and `b` by hand would not even typecheck here.

## Inputs
* `k` – number of extra vertices
* `Z` – zonotope
* `v` – vertex list of the polytope

## Output
* the Minkowski difference of the zonotope and the polytope

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 6]: `Z ⊖ ⟨v⟩_V`, `v` the polytope's `k + 1` vertices, computed by intersecting the
translated zonotopes `Z − v i` one at a time. -/
def ConZonotope.minkDiffV {k : ℕ} (Z : Zonotope (Vec ℝ n)) (v : Fin (k + 1) → Vec ℝ n) :
    ConZonotope (Vec ℝ n) :=
  Fin.foldl k (fun cZ i => cZ.intersection (Z.shift (v i.succ)).conZonotope)
    (Z.shift (v 0)).conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
