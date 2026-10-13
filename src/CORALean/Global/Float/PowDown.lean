module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A directed power, rounded down

`Bᵏ` by repeated `mulDown`: below `xᵏ` for every `x ≥ B ≥ 0`, the lower end of an
enclosure `powUp` is the upper end of.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def powDown (B : 𝕋) : ℕ → 𝕋
  | 0 => one
  | k + 1 => mulDown (powDown B k) B

theorem powDown_le [SoundFloatArithmetic 𝕋] {B : 𝕋} {x : ℝ} (hB0 : 0 ≤ toReal B)
    (hB : toReal B ≤ x) :
    ∀ k : ℕ, toReal (powDown B k) ≤ x ^ k := by -- --- PROOF ---
  intro k
  induction k with
  | zero => simp [powDown, toReal_one]
  | succ k ih =>
    rw [pow_succ, powDown]
    exact le_trans (mulDown_le_mul _ _) (le_trans (mul_le_mul_of_nonneg_right ih hB0)
      (mul_le_mul_of_nonneg_left hB (pow_nonneg (le_trans hB0 hB) k)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
