module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# One halfspace as a comparison

`@stl/polytope2stl.m`, `aux_halfspace2set(x,A,b)`: the row `A` and the bound `b` become the
comparison `A(ind) * x(ind) + ... + A(k) * x(k) op b` over the nonzero entries of `A`, the first
one on its own (`x(ind)` if its coefficient is `1`, `A(ind) * x(ind)` otherwise) and the others
added with the same rule. CORA's `op` is `<=`; the equality rows of `polytope2stl` need `>=`
too. A row with no nonzero entry makes CORA fail (`find` is empty); it is read here as `0 op b`.

Real-only, a specification: it builds a comparison from the coefficients of a halfspace, which the
formula stores as given, so nothing is rounded.
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

/-- `aux_halfspace2set(x,A,b)` of `polytope2stl.m`, for the comparison `op`. -/
noncomputable def STL.Tree.halfspace2set (op : STL.Cmp) (a : Fin n → ℝ) (b : ℝ) : STL.Tree n :=
  let term (i : Fin n) : STL.Expr n := if a i = 1 then .var i else .times (.num (a i)) (.var i)
  match (List.finRange n).filter (fun i => a i ≠ 0) with
  | [] => STL.Tree.compare op (.num 0) (.num b)
  | ind :: rest =>
    let rhs := rest.foldl (fun rhs i => .plus rhs (term i)) (term ind)
    STL.Tree.compare op rhs (.num b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
