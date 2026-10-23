module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A float scalar orders time stamps as reals

The `TimeOrder` of a scalar with an exact comparison: `a ≤ b` is `toReal a ≤ toReal b`, `a < b` its
strict form and `Eqv a b` equality of the reals, each decided by `ExactLe.le`. A signal over `𝕋`
therefore branches exactly as the signal of the reals its stamps denote. Low priority, so a linear
order (ℝ) keeps its own.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ======================================  MAIN INSTANCE  ======================================= --

/-- Time stamps compare as the reals they denote, decided exactly. -/
instance (priority := low) : TimeOrder 𝕋 where
  le a b := toReal a ≤ toReal b
  lt a b := toReal a < toReal b
  Eqv a b := toReal a = toReal b
  decLe a b := decidable_of_iff _ (ExactLe.le_iff a b)
  decLt a b := decidable_of_iff (¬ ExactLe.le b a = true) (by rw [ExactLe.le_iff]; exact not_le)
  decEqv a b := decidable_of_iff (ExactLe.le a b = true ∧ ExactLe.le b a = true)
    (by rw [ExactLe.le_iff, ExactLe.le_iff]; exact le_antisymm_iff.symm)

/-- `≤` of time stamps is `≤` of the reals they denote. -/
theorem le_iff_toReal_le (a b : 𝕋) : a ≤ b ↔ toReal a ≤ toReal b := Iff.rfl

omit [ExactLe 𝕋] in
/-- The time stamp `0` denotes the time `0`. -/
theorem toReal_zero_eq : toReal (0 : 𝕋) = 0 := toReal_zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
