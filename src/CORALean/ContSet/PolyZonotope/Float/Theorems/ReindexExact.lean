module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
public import CORALean.ContSet.PolyZonotope.Float.Operations.Reindex
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# `PolyZonotope.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. It is linear, so it distributes over the Minkowski
sum that `InflatedContSet.construct` is: the relabelled nominal part plus the
relabelled box, with no widening between them.

## Inputs
* `e` – equivalence of dimensions
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* result is the relabelled set
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

theorem PolyZonotope.reindex_exact (e : Fin m ≃ Fin n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (pZ.reindex e).construct = reindexLin e '' pZ.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (pZ.reindex e) + (pZ.I_error.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet pZ + pZ.I_error.construct)
  have h : InflatedContSet.nominalSet (pZ.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet pZ :=
    (Real.PolyZonotope.map_exact (reindexLin e) (InflatedContSet.nominal pZ)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e pZ.I_error, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
