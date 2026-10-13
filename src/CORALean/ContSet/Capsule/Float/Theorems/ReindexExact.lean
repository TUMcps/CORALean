import CORALean.ContSet.Capsule.Float.Operations.Reindex
import CORALean.ContSet.Capsule.Real.Theorems.ReindexExact

/-!
# `Capsule.reindex` is exactly the relabelled set, over a floating-point scalar

The exact layer's `reindex` of the nominal capsule is the nominal capsule of the result, so
`Real.Capsule.reindex_exact` is the equality, as over ℝ: nothing is rounded.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.reindex_exact (e : Fin m ≃ Fin n) (C : Capsule 𝕋 n) :
    (C.reindex e).construct = reindexLin e '' C.construct :=
  Real.Capsule.reindex_exact e C.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
