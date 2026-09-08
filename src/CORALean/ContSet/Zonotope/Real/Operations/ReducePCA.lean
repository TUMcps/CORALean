import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Real.Operations.PCABasis
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

/-!
# `Zonotope.reducePCA`

CORA's `reduce(Z, 'pca', o)` [1]. Its partition is Girard's — CORA reaches it
through `pickedGenerators`, which ranks by `‖g‖₁ - ‖g‖∞` exactly as
`girardSplit` does. What differs is the enclosure: the dropped block is boxed
along the principal axes of the dropped generators themselves, instead of
along the coordinate axes.

There is no fallback branch. `methC` searches for a basis and has to test the
answer, since a selection of generators can be singular; the principal axes
cannot be, being orthonormal, so `pcaBasis_isUnit_det` holds outright and
`reducePCA` is `reduceByBasis` and the order test and nothing else.

Noncomputable, because `pcaBasis` is. That is where the eigendecomposition
sits, and the reason is recorded there.

## References

* [1] `contSet/@zonotope/private/priv_reducePCA.m`, CORA (Sep. 2025). No paper
      behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'pca', o)`: Girard's partition, with the dropped block
boxed along the principal axes of the generators it drops — and nothing at all
at order `o` or below. -/
noncomputable def Zonotope.reducePCA (Z : Zonotope (Vec ℝ n)) (o : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then
    Z.reduceByBasis (Z.girardSplit o hlt) (Z.pcaBasis (Z.girardSplit o hlt))
  else Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
