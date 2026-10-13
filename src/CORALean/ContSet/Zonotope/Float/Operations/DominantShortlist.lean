import CORALean.ContSet.Zonotope.Float.Operations.DetCandidate
import CORALean.ContSet.Zonotope.Float.Operations.DominantLengthFilter
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorMatrix

/-!
# `Zonotope.dominantShortlist`, over a floating-point scalar

Stage two of `dominantDirections`: `priv_generatorVolumeFilter(G, rem)` takes every `n`-subset of
the length-filtered generators (`combinator(cols,rows,'c')`), scores it by the spanned volume
`|det|` of its generators, and keeps the `rem` of largest score (`maxk`). The determinant is
`Zonotope.detCandidate` and the order a ranking by `le`, so a rounded determinant can reorder
subsets whose volumes are close; the subsets are `List.sublistsLen`'s, not the lexicographic ones of
`combinator`.

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

/-- The `L₂` `n`-subsets of the `L₁` longest generators that span the largest volume. -/
def Zonotope.dominantShortlist (Z : Zonotope (Vec 𝕋 n)) (L₁ L₂ : ℕ) : List (List (Fin Z.h)) :=
  let cells := List.sublistsLen n (Z.dominantLengthFilter L₁)           -- combinator(cols,rows,'c')
  let volume := fun T => absolute (Zonotope.detCandidate (Z.generatorMatrix T))  -- parallelogramVol
  (cells.mergeSort fun a b => le (volume b) (volume a)).take L₂         -- maxk(.,rem)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
