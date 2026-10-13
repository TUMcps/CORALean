module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `ZonoBundle.pool`: the generators of every member

The union of the generators of all zonotopes of the bundle, which is what the fil method of
[1, Heuristic fil] picks its `n` directions from ("the union of generators of all zonotopes of the
bundle is used"). One zonotope at the origin carrying them all, member after member.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- All members' generators in one zonotope at the origin, for [1, Heuristic fil]. -/
def ZonoBundle.pool (zB : ZonoBundle (Vec ℝ n)) : Zonotope (Vec ℝ n) where
  h := ∑ i, (zB.Z i).h
  c := 0
  G := fun a => (zB.Z (finSigmaFinEquiv.symm a).1).G (finSigmaFinEquiv.symm a).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
