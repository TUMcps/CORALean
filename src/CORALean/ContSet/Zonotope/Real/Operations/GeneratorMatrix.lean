import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Sort

/-!
# `Zonotope.generatorMatrix`

The `n × n` matrix whose columns are the generators a set `T` of `n` indices names, in the order
of the indices: CORA's `G(:,comb(i,:))` for a row of `combinator(cols,rows,'c')`. A set that does
not have `n` elements gives the zero matrix.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators indexed by `T` (`n` of them, ascending) as columns; `0` if `T` has not `n`
elements. -/
noncomputable def Zonotope.generatorMatrix (Z : Zonotope (Vec ℝ n)) (T : Finset (Fin Z.h)) :
    Mat ℝ n n :=
  if hT : T.card = n then Matrix.of fun i k => Z.G (T.orderEmbOfFin hT k) i else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
