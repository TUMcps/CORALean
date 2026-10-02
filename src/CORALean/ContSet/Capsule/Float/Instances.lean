import CORALean.ContSet.Capsule.Float.Theorems.Convex
import CORALean.ContSet.Capsule.Float.Theorems.IsCompact
import CORALean.ContSet.Capsule.Float.Theorems.ReduceOuter
import CORALean.ContSet.Capsule.Float.Theorems.ReindexExact
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.CompactSet

/-!
# What a float `Capsule` instantiates

`ConvexSet` and `CompactSet`, from the theorems that say so, then `Reduce` (the identity, as CORA's
empty body) and `Reindex` (CORA's `lift_` at a permutation). `ContSet` is in `Capsule`. As over ℝ,
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

instance : Reduce (Capsule 𝕋 n) (Vec ℝ n) where
  reduce := Capsule.reduce
  reduce_outer := Capsule.reduce_outer

instance : Reindex (Capsule 𝕋) where
  reindex := Capsule.reindex
  reindex_exact := Capsule.reindex_exact

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
