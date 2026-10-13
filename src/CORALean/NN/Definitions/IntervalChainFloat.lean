module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A network of interval layers with float weights
`Real.IntervalChain` with the weights and biases stored as floats, for the float interval
backpropagation to run on. An activation is stored as two scalar interval enclosures, `σE` of its
value and `σ'E` of its derivative; what they enclose is not data but a statement
(`IntervalChain.Sound`), as the real functions have no code to run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable (𝕋 : Type) [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

inductive IntervalChain : ℕ → ℕ → Type where
  | nil {n : ℕ} : IntervalChain n n
  | linear {n m k : ℕ} (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (rest : IntervalChain m k) :
      IntervalChain n k
  | act {n k : ℕ} (σE σ'E : Interval 𝕋 → Interval 𝕋) (rest : IntervalChain n k) :
      IntervalChain n k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
