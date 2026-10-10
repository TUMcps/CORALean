import CORALean.ContSet.Zonotope.Real.Operations.DominantShortlist
import CORALean.ContSet.Zonotope.Real.Operations.DominantScore
import Mathlib.Data.List.MinMax

/-!
# `Zonotope.dominantDirections`

CORA's `dominantDirections(Z, filterLength1, filterLength2)` [1]: "the directions that span a
parallelotope which tightly encloses a zonotope". The generators go through `nonzeroFilter`, the
length filter (`filterLength1 = n + 5` of the longest), the generator volume filter
(`filterLength2 = n + 3` subsets of largest `|det|`), and `priv_volumeFilter` picks the subset whose
parallelotope `P box(P⁻¹ Z)` has the least volume; the answer is its `n` generators as columns.
Both lengths are clamped to the number of non-zero generators, as CORA does.

CORA errors where fewer than `n` generators are left (`combinator` of more rows than columns);
here that is `none`. The guarantee "encloses" holds only if the answer is invertible
(`dominantDirections_outer`), which is not always the case (FINDINGS.md).

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `dominantDirections(Z, filterLength1, filterLength2)`: the `n` generators, as columns,
whose parallelotope `P box(P⁻¹ Z)` has the least volume among the `filterLength2` subsets of largest
spanned volume among the `filterLength1` longest generators; `none` where there are none. -/
noncomputable def Zonotope.dominantDirections (Z : Zonotope (Vec ℝ n))
    (filterLength₁ : ℕ := n + 5) (filterLength₂ : ℕ := n + 3) : Option (Mat ℝ n n) :=
  let nrOfGens := (Finset.univ.filter fun j => Z.G j ≠ 0).card    -- size(nonzeroFilter(Z.G),2)
  let L₁ := min filterLength₁ nrOfGens                             -- clamp filterLength1
  let L₂ := min filterLength₂ nrOfGens                             -- clamp filterLength2
  let Gcells := Z.dominantShortlist L₁ L₂                          -- priv_generatorVolumeFilter
  List.argmin Z.dominantScore (Gcells.map Z.generatorMatrix)      -- priv_volumeFilter, 1 pick

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
