module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
public import CORALean.ContSet.ConZonotope.Float.Operations.Reindex
public import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.ConZonotope.Real.Instances

@[expose] public section

/-!
# `ConZonotope.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. It is linear, so it distributes over the Minkowski
sum that `InflatedContSet.construct` is: the relabelled nominal part plus the
relabelled box, with no widening between them.

## Inputs
* `e` – coordinate permutation
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* the reindexed set is the permuted image of the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reindex_exact (e : Fin m ≃ Fin n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (cZ.reindex e).construct = reindexLin e '' cZ.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (cZ.reindex e) + (cZ.I_error.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet cZ + cZ.I_error.construct)
  have h : InflatedContSet.nominalSet (cZ.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet cZ :=
    (Real.ConZonotope.map_exact (reindexLin e) (InflatedContSet.nominal cZ)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e cZ.I_error, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
