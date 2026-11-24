module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A network with its activation slopes held, with float weights
`Real.HeldChain` with the weights and the slopes stored as floats, for the float zonotope batch
backpropagation to run on. The slopes are the floats the forward pass computed, the lines of the
activation layers at the bounds of their input sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable (𝕋 : Type) [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A network with its activation slopes held, with float weights and slopes. -/
inductive HeldChain : ℕ → ℕ → Type where
  | nil {n : ℕ} : HeldChain n n
  | linear {n m k : ℕ} (W : Mat 𝕋 m n) (rest : HeldChain m k) : HeldChain n k
  | slope {n k : ℕ} (s : Vec 𝕋 n) (rest : HeldChain n k) : HeldChain n k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
