import CORALean.ContSet.HPolytope.Real.Operations.AtoAeState
import CORALean.ContSet.HPolytope.Real.Operations.MoveToEq
import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows

/-!
# `HPolytope.compactAtoAe`

CORA's `compact_(P, 'AtoAe')`: after the unit normalization of `compact_` (`normalizeRows`),
every pair of inequality rows `aᵀx ≤ b`, `-aᵀx ≤ -b` becomes the equality `aᵀx = b`
(`priv_compact_toEquality`, its loop in `atoAeState`), the rows moved are deleted from the
inequalities and the equalities are appended (`moveToEq`).

The test for an inverted pair is exact equality of `[a, b]` and `-[a', b']`; CORA's is
`withinTol(sum, 0, tol)` entrywise, at the default `tol = 1e-9`. The emptiness and fullspace
exits at the end of CORA's `compact_` are not needed here, an empty row set being the fullspace.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.compactAtoAe (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) :=
  let Q := P.normalizeRows
  let st := Q.atoAeState
  Q.moveToEq (Finset.univ.filter fun i => i ∉ st.1) st.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
