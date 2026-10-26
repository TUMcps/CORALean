module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The layers a float network can be normalised over
`WeightLayer` with every weight stored as a box of floats, the fused weights of
`getNormalForm` being rounded products: `linear` (`W`, `b`), `elementwiseAffine` (`scale`,
`offset`), `identity` and a pointwise activation, stored as a scalar interval enclosure `f` of the
function it applies. That the boxes and the enclosure hold the real layer's weights and function is
a statement (`WeightLayer.Encloses`), as the real function has no code to run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable (𝕋 : Type) [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- One layer of `n` inputs and `m` outputs, weights in boxes of `𝕋`. -/
inductive WeightLayer : ℕ → ℕ → Type where
  | linear {n m : ℕ} (W : Interval (Mat 𝕋 m n)) (b : Interval (Vec 𝕋 m)) : WeightLayer n m
  | elementwiseAffine {n : ℕ} (scale offset : Interval (Vec 𝕋 n)) : WeightLayer n n
  | identity {n : ℕ} : WeightLayer n n
  | activation {n : ℕ} (f : Interval 𝕋 → Interval 𝕋) : WeightLayer n n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
