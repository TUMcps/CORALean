import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.ConPolyZono.Float.Operations.Reindex
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Instances

/-!
# `ConPolyZono.reindex` is exactly the relabelled set, in float too

An equality, in the layer where every other guarantee is an enclosure, because a
relabelling does no arithmetic. It is linear, so it distributes over the Minkowski
sum that `InflatedContSet.construct` is: the relabelled nominal part plus the
relabelled box, with no widening between them.
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

theorem ConPolyZono.reindex_exact (e : Fin m ≃ Fin n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (cPZ.reindex e).construct = reindexLin e '' cPZ.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (cPZ.reindex e) + (cPZ.err.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet cPZ + cPZ.err.construct)
  have h : InflatedContSet.nominalSet (cPZ.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet cPZ :=
    (Real.ConPolyZono.map_exact (reindexLin e) (InflatedContSet.nominal cPZ)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e cPZ.err, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
