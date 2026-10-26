module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The fused affine map being accumulated, in floats
`WeightAcc` with the fused weights stored as boxes of floats: `id` is nothing fused yet and
`aff W b` the map `x ↦ W x + b` with `W` and `b` the boxes the rounded products give.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable (𝕋 : Type) [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Nothing fused yet, or the fused map `x ↦ W x + b`, in boxes. -/
inductive WeightAcc : ℕ → ℕ → Type where
  | id {n : ℕ} : WeightAcc n n
  | aff {n d : ℕ} (W : Interval (Mat 𝕋 d n)) (b : Interval (Vec 𝕋 d)) : WeightAcc n d

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
