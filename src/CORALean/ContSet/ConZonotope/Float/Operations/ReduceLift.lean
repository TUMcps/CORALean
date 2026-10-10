import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit

/-!
# `ConZonotope.reduceLift` over a floating-point scalar

CORA's `@conZonotope/reduce` [1, Sec. 4.3] with Girard's rule on the stored floats: Girard's
partition of the lifted zonotope at the order `max 1 ((o n + mₑ) / (n + mₑ))`, then
`reduceLiftBy`; at or below that generator count nothing happens. As over ℝ. The ranking is
computed in `𝕋`, so the two layers may keep different generators.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.reduceLift (cZ : ConZonotope 𝕋 n) (o : ℕ) : ConZonotope 𝕋 n :=
  -- the order of the lifted zonotope that leaves `o n + mₑ` generators
  let o' : ℕ := max 1 ((o * n + cZ.P.me) / (n + cZ.P.me))
  if hlt : o' * (n + cZ.P.me) < cZ.h then cZ.reduceLiftBy (cZ.liftEq.girardSplit o' hlt)
  else cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
