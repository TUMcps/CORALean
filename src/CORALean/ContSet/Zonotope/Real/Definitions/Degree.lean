module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# The degree of a point of a zonotope

[1, Sec. 3 (degree)]: `deg(x) := min{dim F | F a face of Z containing x}`. A face of a polytope
is an exposed face, the points maximizing a linear functional (`IsExposed`, which counts `Z`
itself, the zero functional, and `∅`), and its dimension that of its affine hull, the `finrank` of
its `vectorSpan`. Stated for any set, the zonotope being where [1] uses it; for `x ∉ Z` no face
contains `x` and the minimum of the empty set is `0` here.

## Inputs
* `Z` – zonotope as a set
* `x` – point of the zonotope

## Output
* least dimension of a face containing `x`

## References

* [1] [M. Černý. "Goffin's algorithm for zonotopes". Kybernetika,
      2012.](../../../../../../references/2012/cerny-kybernetika-goffin-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3 (degree)]: the least dimension of a face of `Z` containing `x`. -/
noncomputable def Zonotope.degree (Z : Set (Vec ℝ n)) (x : Vec ℝ n) : ℕ :=
  sInf {d | ∃ F : Set (Vec ℝ n), IsExposed ℝ Z F ∧ x ∈ F ∧
    Module.finrank ℝ (vectorSpan ℝ F) = d}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
