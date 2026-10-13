module

public import CORALean.ContSet.Zonotope.Real.Operations.GeneratorMatrix
public import CORALean.ContSet.Zonotope.Real.Operations.DominantLengthFilter
public import Mathlib.Data.List.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# `Zonotope.dominantShortlist`

Stage two of `dominantDirections`: `priv_generatorVolumeFilter(G, rem)` takes every `n`-subset of
the length-filtered generators (`combinator(cols,rows,'c')`), scores it by the spanned volume
`|det|` of its generators, and keeps the `rem` of largest score (`maxk`). Equal scores are ordered
by the sort here and by `maxk` there; the list of subsets is the finset's, not the lexicographic
one of `combinator`.

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

/-- The `L₂` `n`-subsets of the `L₁` longest generators that span the largest volume. -/
noncomputable def Zonotope.dominantShortlist (Z : Zonotope (Vec ℝ n)) (L₁ L₂ : ℕ) :
    List (Finset (Fin Z.h)) :=
  let cells := ((Z.dominantLengthFilter L₁).powersetCard n).toList     -- combinator(cols,rows,'c')
  let volume := fun T => |Matrix.det (Z.generatorMatrix T)|                    -- parallelogramVol
  (cells.mergeSort fun a b => decide (volume b ≤ volume a)).take L₂     -- maxk(.,rem)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
