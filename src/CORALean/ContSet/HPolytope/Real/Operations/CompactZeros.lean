module

public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

@[expose] public section

/-!
# `HPolytope.compactZeros`

CORA's `compact_(P, 'zeros')` (`priv_compact_zeros`): normalize the rows to unit length
(`normalizeRows`, as `compact_` always does first), then look at the rows whose normal is zero.
A zero inequality row `0 ≤ b` with `b < 0`, or a zero equality row `0 = be` with `be ≠ 0`, is
infeasible and the result is the empty set; all other zero rows constrain nothing and are
deleted. What is left is `restrict`ed to the nonzero rows; with none left it is the fullspace.
The tolerance is `0`: CORA's `withinTol(·, 0, tol)` also calls a row zero within `tol = 1e-9`,
and an offset `b < 0` with `|b| < tol` is not infeasible there.

## Inputs
* `P` – H-polytope

## Output
* `P` normalized without its zero rows, or the empty set if one is infeasible
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.compactZeros (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) :=
  let Q := P.normalizeRows
  if (∃ i, Q.A i = 0 ∧ Q.b i < 0) ∨ ∃ r, Q.Ae r = 0 ∧ Q.be r ≠ 0 then
    HPolytope.emptySet (Vec ℝ n)
  else Q.restrict (Finset.univ.filter fun i => Q.A i ≠ 0) (Finset.univ.filter fun r => Q.Ae r ≠ 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
