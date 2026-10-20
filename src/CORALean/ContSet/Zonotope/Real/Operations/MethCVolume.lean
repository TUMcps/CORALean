module

public import CORALean.ContSet.Zonotope.Real.Operations.MethCFilter
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# `Zonotope.methCVolume`

The objective stage two of `methC` maximizes: `abs(det(Gpicked))` [1], the
volume of the parallelepiped that `n` of the filtered generators span. It is a
plain `|det|` of the square selection, not a Gram determinant — the selection
is already `n × n`, one column per picked generator.

A selection is an embedding `Fin n ↪ Fin (min (n + 8) r)`, so it names `n`
distinct candidates. `|det|` is unchanged by reordering them, so ranking
embeddings ranks the subsets CORA's `combinator(cols,rows,'c')` enumerates.

## Inputs
* `Z` – zonotope
* `part` – split of the generators
* `e` – selection of filtered generators

## Output
* volume spanned by the selected generators

## References

* [1] `contSet/@zonotope/private/priv_generatorVolumeFilter.m:44`, CORA
      (Sep. 2025). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The volume `n` filtered generators span, `|det|` of the matrix whose
columns they are. -/
noncomputable def Zonotope.methCVolume (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r))
    (e : Fin n ↪ Fin (min (n + 8) r)) : ℝ :=
  |(Matrix.of fun i k => Z.G (Z.methCFilter part (e k)) i : Mat ℝ n n).det|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
