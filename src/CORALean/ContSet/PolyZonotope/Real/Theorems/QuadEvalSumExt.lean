import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

/-!
# A quadratic map of the extended sum, expanded over pairs

`bilin_point` at `quadBilin`, read back over the extended sum: the expansion
over pairs of generators, and the monomial arithmetic that makes each pair a
monomial again, are the shared pairing's and are not redone here. `quadEval` at
one point is `quadBilin` at it twice, definitionally, and `quadMapDep`'s own
point is the sum on the right with an empty centre.

Pointwise in the factor vector, and public for that reason: the constrained
representation needs it at a fixed `a`, which a set equality cannot give.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The map of a sum, expanded over pairs: `bilin_point` at `quadBilin`, whose
point is the same sum with an empty centre. -/
theorem PolyZonotope.quadEval_sum_ext (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) :
    quadEval Q (∑ l, extM pZ a l • extG pZ l)
      = ∑ l, monomial (quadMapE pZ) a l • quadMapG Q pZ l := by -- --- PROOF ---
  -- the ascription is `bilin_point`'s statement with `quadMapDep`'s fields unfolded
  have h : quadEval Q (pZ.c + ∑ i, monomial pZ.E a i • pZ.G i)
      = (0 : Vec ℝ m) + ∑ l, monomial (quadMapE pZ) a l • quadMapG Q pZ l :=
    (PolyZonotope.bilin_point (PolyZonotope.quadBilin Q) pZ pZ rfl a).symm
  rw [PolyZonotope.sum_ext_eq_point pZ a, h, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
