import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLiftBy
import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit

/-!
# `ConZonotope.reduceLift`

CORA's `@conZonotope/reduce` [1, Sec. 4.3] with Girard's rule, the one `Zonotope.reduce`
uses here. CORA asks for the lifted zonotope the order `max(1, (o n + mₑ) / (n + mₑ))`, which
is the degree-of-freedom order `o` of the constrained zonotope in the larger dimension;
the quotient is rounded down, so the lifted zonotope never keeps more than `o n + mₑ`
generators. At or below that count nothing happens and the set is returned as it is.

With no equalities the lifted zonotope is the enclosing zonotope, the order is `o`, and the
reduction is `Zonotope.reduceGirard`'s, the inequality rows kept on the kept generators.
Beside `reduce`, not in place of it: that one forgets every constraint.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(cZ, 'girard', o)`: Girard's partition of the lifted zonotope `[G; Aₑ]`,
at the order `max 1 ((o n + mₑ) / (n + mₑ))` CORA scales `o` to. -/
noncomputable def ConZonotope.reduceLift (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  -- the order of the lifted zonotope that leaves `o n + mₑ` generators
  let o' : ℕ := max 1 ((o * n + cZ.P.me) / (n + cZ.P.me))
  if hlt : o' * (n + cZ.P.me) < cZ.h then
    cZ.reduceLiftBy (cZ.liftEq.zonotope.girardSplit o' hlt)
  else cZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
