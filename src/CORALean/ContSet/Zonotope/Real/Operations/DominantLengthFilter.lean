module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.dominantLengthFilter`

Stage one of `dominantDirections`: `priv_lengthFilter(G, rem)` keeps the `rem` generators of largest
Euclidean length (`maxk(vecnorm(G), rem)`). Squaring is monotone, so the ranking is by the sum of
squares, as in `methCFilter`. Among equally long generators the sort decides; CORA's `maxk` its own
order.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` longest generators, as a set of indices: the first `k` of the descending sort by
length. -/
noncomputable def Zonotope.dominantLengthFilter (Z : Zonotope (Vec ℝ n)) (k : ℕ) :
    Finset (Fin Z.h) :=
  (Finset.univ.filter fun p : Fin Z.h => (p : ℕ) < k).image
    (Tuple.sort fun j => -∑ i, (Z.G j i) ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
