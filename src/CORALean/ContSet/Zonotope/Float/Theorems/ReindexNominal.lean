import CORALean.ContSet.Zonotope.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# A relabelled zonotope's nominal part is the exact layer's `map` at the relabelling

Definitional: `nominal` reads each generator into ℝ, which commutes with
moving the coordinate axis.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Definitional: `nominal` reads each generator into ℝ, which commutes with
moving the coordinate axis. -/
theorem Zonotope.reindex_nominal (e : Fin m ≃ Fin n) (Z : Zonotope (Vec 𝕋 n)) :
    InflatedContSet.nominal (Z.reindex e)
      = Real.Zonotope.map (reindexLin e) (InflatedContSet.nominal Z) := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
