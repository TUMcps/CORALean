import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Float.Layers.Curvature
import CORALean.NN.Layers.Tanh

/-!
# The tanh layer over a floating-point scalar

`tanh t = 2 σ(2t) - 1`: `Relaxation.ofAffineConj` transports `sigmoidRelaxation`
wholesale, rather than a second exponential enclosure or a second derivative
bracket built for `tanh` directly.

`FloatOps` has no float that denotes `2` exactly, so both `2`s round through
`doubleRounding` — self-addition, not a stored constant. `-1` needs no such
care: `neg one` is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Doubling by self-addition: exact in any binary format, and it needs no
float that denotes `2`. -/
def doubleRounding : ScaleRounding 𝕋 2 where
  up x := addUp x x
  down x := addDown x x
  up_ge x := by have h := add_le_addUp x x; linarith
  down_le x := by have h := addDown_le_add x x; linarith

/-- `sigmoidRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
noncomputable def tanhRelaxation (k : ℕ) : Relaxation 𝕋 Real.tanh :=
  (sigmoidRelaxation k).ofAffineConj doubleRounding doubleRounding (neg one)
    (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

/-- `k` is the reduction depth the sigmoid relaxation underneath is built at. -/
noncomputable def tanh (k : ℕ) : Real.Layer S n n := Layer.activation (tanhRelaxation k)

end Layer

end CORALean.Float
