module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.generatorMatrix`, over a floating-point scalar

The `n × n` matrix whose columns are the stored generators a list `T` of `n` indices names, in the
order of the list: CORA's `G(:,comb(i,:))` for a row of `combinator(cols,rows,'c')`. A list that
does not have `n` entries gives the zero matrix. Every entry is a stored float, so nothing rounds.

Source: [1].

## Inputs
* `Z` – zonotope
* `T` – generator indices

## Output
* selected generators as columns, zero without `n` entries

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

/-- The generators indexed by `T` (`n` of them) as columns; `0` if `T` has not `n` entries. -/
def Zonotope.generatorMatrix (Z : Zonotope (Vec 𝕋 n)) (T : List (Fin Z.h)) : Mat 𝕋 n n :=
  if hT : T.length = n then fun i k => Z.G (T.get (k.cast hT.symm)) i else fun _ _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
