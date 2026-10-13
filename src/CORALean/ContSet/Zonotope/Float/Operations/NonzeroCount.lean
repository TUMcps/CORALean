module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.nonzeroCount`

`size(nonzeroFilter(Z.G),2)`: how many stored generators are not zero. A generator counts as zero
when every entry is known to be `≤ 0` in magnitude (`le` certifies `≤` only), so a generator `le`
cannot confirm to be zero is kept, as `nonzeroFilter` keeps it.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The number of generators that are not provably zero. -/
def Zonotope.nonzeroCount (Z : Zonotope (Vec 𝕋 n)) : ℕ :=
  ((List.finRange Z.h).filter fun j =>
    !(List.finRange n).all fun i => le (absolute (Z.G j i)) zero).length

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
