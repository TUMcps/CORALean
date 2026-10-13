import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Operations.PadCoeffs
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Padded coefficients read back as the exact padding

The padded slot is the only one that moves, and `zero` reads as `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_padCoeffs (c : Fin (k + 1) → 𝕋) (M : ℕ) (j : Fin (M + 1)) :
    toReal (padCoeffs c M j) = Real.padCoeffs (fun i => toReal (c i)) M j := by -- --- PROOF ---
  show toReal (if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else zero)
    = if h : (j : ℕ) < k + 1 then toReal (c ⟨(j : ℕ), h⟩) else 0
  -- the padded slot is the only one that moves, and `zero` reads as `0`
  by_cases h : (j : ℕ) < k + 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, toReal_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
