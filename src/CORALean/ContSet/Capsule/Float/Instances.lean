import CORALean.ContSet.Capsule.Float.Theorems.Convex
import CORALean.ContSet.Capsule.Float.Theorems.IsCompact
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.CompactSet

/-!
# What a float `Capsule` instantiates

`ConvexSet` and `CompactSet`, from the theorems that say so. `ContSet` is in `Capsule`. As over ℝ,
no `Plus`, `Mtimes` or `LinComb`: a capsule is closed under almost nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ConvexSet (Capsule 𝕋 n) (Vec ℝ n) := ⟨Capsule.convex_construct⟩

instance : CompactSet (Capsule 𝕋 n) (Vec ℝ n) := ⟨Capsule.isCompact_construct⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
