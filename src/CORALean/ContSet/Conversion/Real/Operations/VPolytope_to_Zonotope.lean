module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.Zonotope.Real.Operations.EnclosePointsMaiga
public import CORALean.ContSet.Zonotope.Real.Operations.CompactZeros
public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.Global.MatVec

@[expose] public section

/-!
# A matrix polytope as a matrix zonotope

CORA's `@matPolytope/matZonotope`: the vertices stacked into the columns of a point cloud, enclosed
by `zonotope.enclosePoints` (its default `'maiga'`), the zero generators dropped (`compact(·,
'zeros')`), and the center and generators reshaped back into matrices. The principal-direction
oracle `dir` of the `'maiga'` algorithm (`svd(X)(:, 1)` in CORA) has no algorithm here and is an
argument; the result is CORA's for that oracle. At least one vertex.

## Inputs
* `P` – matrix vertex polytope
* `dir` – direction chosen from the vertices

## Output
* matrix zonotope enclosing the vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `matZ = matZonotope(matP)`: a matrix zonotope enclosing the vertices of the polytope. -/
noncomputable def VPolytope.matZonotope (P : VPolytope (Mat ℝ m n)) [NeZero P.k]
    (dir : (Fin P.k → Vec ℝ (n * m)) → Vec ℝ (n * m)) : Zonotope (Mat ℝ m n) :=
  -- 1. `V = reshape(matV, [], size(matV, 3))`, one column per vertex
  let V : Fin P.k → Vec ℝ (n * m) := fun l => matVecEquiv (P.V l)
  -- 2. `Z = compact(zonotope.enclosePoints(V), 'zeros')`
  let Z := (Zonotope.enclosePointsMaiga dir V).compactZeros
  -- 3. `C = reshape(Z.c, size(matP))` and `G = reshape(Z.G, [size(matP), size(Z.G, 2)])`
  Z.map matVecEquiv.symm.toLinearMap

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
