module

public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import Mathlib.Order.Lex
public import Mathlib.Data.Prod.Lex

@[expose] public section

/-!
# `HPolytope.compactAlignedIneq`

CORA's `priv_compact_alignedIneq`, the inequality half of `compact_(P, 'aligned')`: after the unit
normalization of `compact_` (`normalizeRows`), rows with the same normal vector `a` are merged into
the one with the smallest right-hand side. The smallest row of each run is kept, the others deleted
by `restrict`. The test for equal normals is exact equality; CORA's is `sum(abs(a - a')) < tol` at
`tol = 1e-9`, which also merges merely close normals. The equality half, and `'Ae'`, is not
formalized: CORA's `priv_compact_alignedEq` is wrong for a zero equality row
(`references/coverage/contSet/polytope.md`), "aligned" with all rows: `Ae = [0 0; 1 0]`,
`be = [0; 1]` comes out empty.

## Inputs
* `P` – H-polytope

## Output
* `P` normalized, rows with a common normal merged into the one with smallest bound
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

noncomputable def HPolytope.compactAlignedIneq (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) :=
  let Q := P.normalizeRows
  Q.restrict (Finset.univ.filter fun i =>
      ∀ j, Q.A j = Q.A i → toLex (Q.b i, i) ≤ toLex (Q.b j, j)) Finset.univ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
