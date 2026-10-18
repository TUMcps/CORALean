module

public import CORALean.ContSet.Capsule.Float.Operations.Reindex
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.ReindexExact
public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Float.Theorems.ReindexExact

@[expose] public section

/-!
# `Capsule.reindex` is exactly the relabelled set, over a floating-point scalar

The exact layer's `reindex` of the nominal capsule is the nominal capsule of the result, and the
box is relabelled exactly (`Interval.reindex_exact`); relabelling is linear, so it maps the sum of
the two to the sum of their images. Nothing is rounded.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact layer's `reindex` of the nominal capsule is the nominal capsule of the result, and
the box is relabelled exactly, so the equality holds, as over ℝ: nothing is rounded. -/
theorem Capsule.reindex_exact (e : Fin m ≃ Fin n) (C : Capsule 𝕋 n) :
    (C.reindex e).construct = reindexLin e '' C.construct := by
  show InflatedContSet.nominalSet (C.reindex e) + (C.I_error.reindex e).construct
    = reindexLin e '' (InflatedContSet.nominalSet C + C.I_error.construct)
  rw [InflatedContSet.image_add, Interval.reindex_exact e C.I_error]
  exact congrArg (· + _) (Real.Capsule.reindex_exact e C.nominal)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
