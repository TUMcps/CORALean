import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.dominantLengthFilter`, over a floating-point scalar

Stage one of `dominantDirections`: `priv_lengthFilter(G, rem)` keeps the `rem` generators of
largest Euclidean length (`maxk(vecnorm(G), rem)`). Squaring is monotone, so the ranking is by the
sum of squares, rounded up. `le` has no order laws, so this is a ranking and not a `List.argmax`:
a misranking changes which generators are kept and nothing about what is enclosed. The kept indices
stay in their own order.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` longest generators, as indices in increasing order. -/
def Zonotope.dominantLengthFilter (Z : Zonotope (Vec 𝕋 n)) (k : ℕ) : List (Fin Z.h) :=
  let len := fun j => sumUp fun i => mulUp (Z.G j i) (Z.G j i)               -- sum(G.^2, 1)
  let top := ((List.finRange Z.h).mergeSort fun a b => le (len b) (len a)).take k  -- maxk
  (List.finRange Z.h).filter fun j => decide (j ∈ top)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
