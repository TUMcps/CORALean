module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.VPolytope.Real.Operations.Bilin
public import CORALean.ContSet.VPolytope.Real.Operations.ColLin
public import CORALean.ContSet.VPolytope.Real.Operations.Map
public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.Global.MatVec

@[expose] public section

/-!
# `ContSet/VPolytope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix CORALean

variable {n m : ℕ}


-- ================================  `VPolytope.enclosePoints`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@polytope/enclosePoints`: the polytope spanned by a finite family of points. CORA runs a
QR reduction and `convhulln` to keep only the extreme points, which changes the vertex list and
not the set; the vertex description of the whole family denotes the same hull. -/
def VPolytope.enclosePoints {N : ℕ} (pts : Fin N → Vec ℝ n) : VPolytope (Vec ℝ n) :=
  ⟨N, pts⟩


-- ====================================  `VPolytope.matMul`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `matPolytope * matPolytope`: every product of a vertex of the first and one of the
second. -/
def VPolytope.matMul {p q r : ℕ} (P : VPolytope (Mat ℝ p q)) (Q : VPolytope (Mat ℝ q r)) :
    VPolytope (Mat ℝ p r) :=
  VPolytope.bilin matMulBilin P Q


-- =================================  `VPolytope.matPolytope`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `matPolytope(P)`: each vertex `v` of the polytope read as the `n × 1` matrix with that
column, the matrix polytope of those. A vertex list is mapped by the linear embedding of a vector
as a column. -/
def VPolytope.matPolytope (P : VPolytope (Vec ℝ n)) : VPolytope (Mat ℝ n 1) :=
  P.map (colLin n)


-- ===================================  `VPolytope.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@polytope/project`: the vertices at the chosen coordinates (`V(dims,:)` in CORA). `dims`
may repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the
selection map, and `project_exact` is `map_exact`. -/
def VPolytope.project (P : VPolytope (Vec ℝ n)) (dims : Fin m → Fin n) : VPolytope (Vec ℝ m) :=
  P.map (LinearMap.funLeft ℝ ℝ dims)


-- =====================================  `VPolytope.vec`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `polytope(matP)`: each vertex matrix stacked column by column (`reshape(·, [], 1)`). -/
def VPolytope.vec (P : VPolytope (Mat ℝ n m)) : VPolytope (Vec ℝ (m * n)) :=
  P.map matVecEquiv.toLinearMap


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
