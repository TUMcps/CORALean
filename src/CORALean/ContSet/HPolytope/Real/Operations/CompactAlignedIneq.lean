import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
import CORALean.ContSet.HPolytope.Real.Operations.Restrict
import Mathlib.Order.Lex
import Mathlib.Data.Prod.Lex

/-!
# `HPolytope.compactAlignedIneq`

CORA's `priv_compact_alignedIneq`, the inequality half of `compact_(P, 'aligned')` (and a step
of `'A'` and `'all'`): after the unit normalization of `compact_` (`normalizeRows`), rows with
the same normal vector `a` are merged into the one with the smallest right-hand side. CORA
sorts the rows and walks the runs of equal normals; here the row kept in each run is the one
with the smallest pair `(b, index)`, the others are deleted by `restrict`, so the kept rows
keep their original order where CORA's come out sorted by normal vector.

The test for equal normals is exact equality; CORA's is `sum(abs(a - a')) < tol`, which at the
default `tol = 1e-9` also merges normals that are merely close, under the smaller `b`.
The equality rows are untouched.

The equality half of `'aligned'`, and `'Ae'`, is not formalized, as CORA's
`priv_compact_alignedEq` is wrong when an equality row is zero (FINDINGS.md): its alignment test
`Ae(i,:) - (Ae*Ae(i,:)')*Ae(i,:) = 0` holds for every row `j` once `Ae(i,:) = 0`, so a zero row
is "aligned" with all rows; `Ae = [0 0; 1 0]`, `be = [0; 1]`, the set `x₁ = 1`, comes out empty.
`'all'` removes zero rows first (`compactZeros`).
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

noncomputable def HPolytope.compactAlignedIneq (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) :=
  let Q := P.normalizeRows
  Q.restrict (Finset.univ.filter fun i =>
      ∀ j, Q.A j = Q.A i → toLex (Q.b i, i) ≤ toLex (Q.b j, j)) Finset.univ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
