import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.NN.Layers.Layer

/-!
# The linear layer

CORA's `nnLinearLayer`: `x ↦ W x + b`, with `W` and `b` stored in the scalar. The only layer
whose propagation is a set operation and nothing else — `mtimes` for the weights, `plus` with
the bias — so the only standard one that loses nothing at a representation closed under both.

The bias enters as a box of zero width rather than through an operation of its own, which is
why `OfInterval` is asked for here and not a translation: a representation that can absorb a
box can absorb a point. Nothing rounds here either: both operations already pay their own
rounding into the representation, and a layer that added one of its own would pay twice. What
the layer encloses is the exact affine map the stored weights denote — reading a network off a
file is exact; everything after it rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes Float.OfInterval

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.linear (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Float.Interval.point b))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
