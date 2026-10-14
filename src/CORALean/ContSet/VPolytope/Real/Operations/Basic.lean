module

public import CORALean.ContSet.VPolytope.Real.Operations.ColLin
public import CORALean.ContSet.VPolytope.Real.Operations.Map
public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `ContSet/VPolytope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ================================  `VPolytope.enclosePoints`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@polytope/enclosePoints`: the polytope spanned by a finite family of points. CORA runs a
QR reduction and `convhulln` to keep only the extreme points, which changes the vertex list and
not the set; the vertex description of the whole family denotes the same hull. -/
def VPolytope.enclosePoints {N : ℕ} (pts : Fin N → Vec ℝ n) : VPolytope (Vec ℝ n) :=
  ⟨N, pts⟩

end CORALean.Real


-- =================================  `VPolytope.matPolytope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `matPolytope(P)`: each vertex `v` of the polytope read as the `n × 1` matrix with that
column, the matrix polytope of those. A vertex list is mapped by the linear embedding of a vector
as a column. -/
def VPolytope.matPolytope (P : VPolytope (Vec ℝ n)) : VPolytope (Mat ℝ n 1) :=
  P.map (colLin n)

end CORALean.Real


-- ================================  `VPolytope.mtimes_eq_map`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem VPolytope.mtimes_eq_map (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    VPolytope.mtimes M P = P.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ===================================  `VPolytope.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- CORA's `@polytope/project`: the vertices at the chosen coordinates (`V(dims,:)` in CORA). `dims`
may repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the
selection map, and `project_exact` is `map_exact`. -/
def VPolytope.project (P : VPolytope (Vec ℝ n)) (dims : Fin m → Fin n) : VPolytope (Vec ℝ m) :=
  P.map (LinearMap.funLeft ℝ ℝ dims)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
