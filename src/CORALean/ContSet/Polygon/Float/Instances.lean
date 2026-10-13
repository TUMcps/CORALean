import CORALean.ContSet.Polygon.Float.Theorems.LinCombOuter

/-!
# What the float `Polygon` instantiates

`ContSet`, `Plus` and `Reduce` come from `SetUnion` at the float polytope, which has them;
`LinComb` is this layer's own.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] : LinComb (Polygon 𝕋) (Vec ℝ 2) where
  linComb := Polygon.linComb
  linComb_outer := Polygon.linComb_outer

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
