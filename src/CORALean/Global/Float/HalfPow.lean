module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Halving `k` times

Halving is exact (`toReal_half`), so `halfPow k x` is `x / 2ᵏ` as a real, with no rounding: the
way a power of two divides without a `divUp`.

## Inputs
* none

## Output
* the function halving a float `k` times
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def halfPow : ℕ → 𝕋 → 𝕋
  | 0, x => x
  | k + 1, x => half (halfPow k x)

theorem toReal_halfPow [SoundFloatArithmetic 𝕋] (k : ℕ) (x : 𝕋) :
    toReal (halfPow k x) = toReal x / 2 ^ k := by
  induction k with
  | zero => simp [halfPow]
  | succ k ih => rw [halfPow, toReal_half, ih, pow_succ, div_div]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
