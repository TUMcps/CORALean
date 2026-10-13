import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Operations.OnePlusExpDown

/-!
# The logistic function at a stored value

`σ` at a stored value, over `Global/Float`'s `expDown` and the division a logistic function is.
It is all the sigmoid layer needs: `σ' t = σ t · σ (-t)`, so the same enclosure at a box's ends
brackets the derivative too. The enclosure is total, which is a choice of *which* identity to
compute each side from: `expUp` needs its argument bounded and `expDown` does not, so both use
`expDown` — `σ t ≤ 1 / D` for any `0 < D ≤ 1 + e⁻ᵗ` above, and `σ t = 1 - 1 / (1 + eᵗ)`
below. `k` is the exponential's reduction depth: every `k` is sound, a larger one tighter.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both ends from `expDown`: `1 - 1/(1 + eᵗ)` below, `1/(1 + e⁻ᵗ)` above. -/
def sigmoidEnclosure (k : ℕ) : Enclosure 𝕋 where
  lo a := subDown one (divUp one (onePlusExpDown k a))
  hi a := divUp one (onePlusExpDown k (neg a))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
