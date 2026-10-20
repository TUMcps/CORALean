module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.Specification.STL.Operations.TreeHalfspace2set
public import CORALean.Specification.STL.Operations.TreeConjoin

@[expose] public section

/-!
# polytope2stl, with the equalities

`@stl/polytope2stl.m` extended by the rows of `P.Ae` and `P.be`, each as the two comparisons
`<=` and `>=` (`STL.Tree` has no equality node). The printed version, which drops them, is
`STL.Tree.polytope2stlCora`.

Real-only, a specification: it builds a formula from the rows of a polytope, whose coefficients
the formula stores as given, so nothing is rounded.

## Inputs
* `P` – polytope

## Output
* the formula for the polytope including its equalities
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

/-- `polytope2stl(obj,P)` for `{x | A x <= b, Ae x = be}`. -/
noncomputable def STL.Tree.polytope2stl (P : Real.HPolytope (Fin n → ℝ)) : STL.Tree n :=
  STL.Tree.conjoin ((List.finRange P.m).map (fun i =>
      STL.Tree.halfspace2set .le (fun j => P.A i (Pi.single j 1)) (P.b i)) ++
    (List.finRange P.me).flatMap fun i => [.le, .ge].map fun op =>
      STL.Tree.halfspace2set op (fun j => P.Ae i (Pi.single j 1)) (P.be i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
