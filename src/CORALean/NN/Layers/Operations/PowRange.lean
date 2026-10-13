module

public import CORALean.NN.Layers.Operations.MulRangeDown
public import CORALean.NN.Layers.Operations.MulRangeUp

@[expose] public section

/-!
# A power bracketed

`t ^ k` bracketed, both ends carried together since each end of `t ^ (k + 1)` reads both ends
of `t ^ k`. `one` is exact, so the empty product pays no rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `t ^ k` bracketed, both ends carried together since each reads both. -/
def powRange (t : 𝕋) : ℕ → 𝕋 × 𝕋
  | 0 => (one, one)
  | k + 1 => (mulRangeDown t (powRange t k).1 (powRange t k).2,
      mulRangeUp t (powRange t k).1 (powRange t k).2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
