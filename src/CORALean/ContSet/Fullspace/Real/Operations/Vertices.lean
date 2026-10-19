module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.Global.Corners
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `Fullspace.vertices`

CORA's `@fullspace/vertices_` [1]: `vertices_(interval(fs))`, the `2^n` corners of the box
`[-Inf, Inf]^n` as a matrix of `±Inf` (an error at `n = 0`). A point at infinity is not a vector
of `ℝ^n`, so a column here is a vector of `EReal` with every entry `⊥` or `⊤`, in the order of
`Interval.vPolytope`'s corners (`signEquiv`): a corner takes `⊤` where its sign says "upper".
The dimension is `n + 1`, since CORA throws at `n = 0`.

The full space has no extreme points, so these columns are not vertices of the set; what they are
is the limit of the vertices of the truncated boxes `[-t, t]^n` (`Fullspace.truncatedVertices`),
whose hulls exhaust the space (`Fullspace.construct_eq_iUnion_truncatedVertices`).

## Inputs
* `_` – full space
* `l` – corner index

## Output
* the `l`-th corner, each entry `⊥` or `⊤`

## References

* [1] `contSet/@fullspace/vertices_.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/vertices_`: the `2^(n+1)` corners of `[-Inf, Inf]^(n+1)`, one per sign pattern. -/
noncomputable def Fullspace.vertices (_ : Fullspace (n + 1)) (l : Fin (2 ^ (n + 1))) :
    Fin (n + 1) → EReal :=
  fun j => if signEquiv (n + 1) l j then ⊤ else ⊥

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
