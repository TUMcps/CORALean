module

public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
public import CORALean.ContSet.Zonotope.Float.Operations.Reindex
public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `Zonotope.reindex` is exactly the relabelled zonotope, in float too

An equality, in the layer where every other guarantee is an enclosure, and the
reason is that a relabelling does no arithmetic.

What the float layer adds is the error box, and it costs nothing here either. A
reindexing is linear, so it distributes over the Minkowski sum that
`InflatedContSet.construct` is — the relabelled set is the relabelled nominal
part plus the relabelled box, with no widening between them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reindex_exact (e : Fin m ≃ Fin n) (Z : Zonotope (Vec 𝕋 n)) :
    (Z.reindex e).construct = reindexLin e '' Z.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (Z.reindex e) + (Z.E.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet Z + Z.E.construct)
  have h : InflatedContSet.nominalSet (Z.reindex e)
      = reindexLin e '' InflatedContSet.nominalSet Z :=
    (Real.Zonotope.map_exact (reindexLin e) (InflatedContSet.nominal Z)).symm
  rw [InflatedContSet.image_add, Interval.reindex_exact e Z.E, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
