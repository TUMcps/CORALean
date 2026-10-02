import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.PolyZonotope.Float.Operations.Reindex
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# `PolyZonotope.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. It is linear, so it distributes over the Minkowski
sum that `InflatedContSet.construct` is: the relabelled nominal part plus the
relabelled box, with no widening between them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reindex_exact (e : Fin m ≃ Fin n) (pZ : PolyZonotope 𝕋 n) :
    (pZ.reindex e).construct = reindexLin e '' pZ.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (pZ.reindex e) + (pZ.err.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet pZ + pZ.err.construct)
  have h : InflatedContSet.nominalSet (pZ.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet pZ :=
    (Real.PolyZonotope.map_exact (reindexLin e) (InflatedContSet.nominal pZ)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e pZ.err, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
