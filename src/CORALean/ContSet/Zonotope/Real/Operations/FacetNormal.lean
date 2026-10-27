module

public import CORALean.Global.CrossProduct
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# One row of [1, Thm. 2]'s `C`

The normal the theorem attaches to a choice of `n` generators out of `p`: their `n`-dimensional
cross product, [1, Def. 2]'s `nX`, at the matrix holding those generators as columns.
Unnormalized, where the printed `C⁽ⁱ⁾ = nX(...)ᵀ / ‖nX(...)‖₂` divides by the length: a halfspace
is unchanged by scaling its normal and its offset together, and `Δd = ∑ |C G⁽ᵘ⁾|` scales with
`C`, so the two describe the same set. The `2·C(p, n-1)` rows of the printed `C` are these
`C(p, n-1)` normals and their negatives, which is why every statement over them takes an absolute
value. The rows first appeared in [2, Thm. 7] and, at `p = n`, [2, Lemma 6].

## Inputs
* `n` – dimension minus one
* `Z` – zonotope
* `S` – selected generator indices

## Output
* cross product of the selected generators

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 2]'s normal at the `n` generators `S` selects: their cross product. -/
def Zonotope.facetNormal {n : ℕ} (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h) :
    Vec ℝ (n + 1) :=
  nCross (Matrix.of fun i j => Z.G (S j) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
