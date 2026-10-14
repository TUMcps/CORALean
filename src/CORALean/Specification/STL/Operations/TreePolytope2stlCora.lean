module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.Specification.STL.Operations.TreeHalfspace2set
public import CORALean.Specification.STL.Operations.TreeConjoin

@[expose] public section

/-!
# polytope2stl, as printed

`@stl/polytope2stl.m` loops over the rows of `P.A` and `P.b` only: the equality constraints
`P.Ae x = P.be` of the polytope are dropped. A polytope that has them (the single point a vertex
polytope converts to, a flat polytope) is converted to a formula satisfied outside it. The
coefficient of `x(j)` in row `i` is `P.A i (e_j)`; see `STL.Tree.polytope2stl` for the version
that
keeps the equalities, and `STL.Tree.polytope2stlCora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polytope2stl(obj,P)`, inequality rows only, as printed. -/
noncomputable def STL.Tree.polytope2stlCora (P : Real.HPolytope (Fin n → ℝ)) : STL.Tree n :=
  STL.Tree.conjoin ((List.finRange P.m).map fun i =>
    STL.Tree.halfspace2set .le (fun j => P.A i (Pi.single j 1)) (P.b i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
