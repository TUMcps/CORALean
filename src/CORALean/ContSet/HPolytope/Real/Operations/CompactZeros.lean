import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
import CORALean.ContSet.HPolytope.Real.Operations.Restrict
import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

/-!
# `HPolytope.compactZeros`

CORA's `compact_(P, 'zeros')` (`priv_compact_zeros`): normalize the rows to unit length
(`normalizeRows`, as `compact_` always does first), then look at the rows whose normal vector is
zero. A zero inequality row `0 ≤ b` with `b < 0`, or a zero equality row `0 = be` with
`be ≠ 0`, is infeasible and the result is the empty set; all other zero rows constrain nothing
and are deleted. What is left is `restrict`ed to the nonzero rows; with none left it is the
fullspace, CORA's `polytope.Inf(n)`.

The tolerance is `0`: CORA's `withinTol(·, 0, tol)` calls a row zero if it is within `tol` of
zero, the default being `1e-9`, and an offset `b` with `b < 0` but `|b| < tol` is not infeasible.
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
