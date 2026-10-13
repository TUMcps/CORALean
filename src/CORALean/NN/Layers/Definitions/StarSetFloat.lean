import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Definitions.StarSet

/-!
# The star set over a float scalar

`Real.StarSet` with its numbers stored in the scalar `𝕋`: the tuple `(c, G, C, d, l, u)` of
CORA's `conversionConZonoStarSet`, the constraints kept as a list of rows `(a, b)`, `a · α ≤ b`.
Its denotation is `ContSet (StarSet 𝕋 n)`, in `Operations/StarSetFloatContSet.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A star set stored in `𝕋`: `m` factors, centre `c`, generators `G`, constraint rows, and the
box `[l, u]` of the factors. -/
structure StarSet (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (n : ℕ) where
  m : ℕ
  c : Fin n → 𝕋
  G : Fin n → Fin m → 𝕋
  cons : List ((Fin m → 𝕋) × 𝕋)
  l : Fin m → 𝕋
  u : Fin m → 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
