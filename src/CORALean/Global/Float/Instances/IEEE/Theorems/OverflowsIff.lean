module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import CORALean.Global.Float.Instances.IEEE.Operations.Overflows

@[expose] public section

/-!
# What `overflows` detects

Exactly the values past the format's range: `|x| > maxFinite`, compared through
`Dyadic.le_iff` with no rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem overflows_iff (x : IEEE fmt) :
    overflows x = true ↔ ((fmt.maxFinite : ℚ) : ℝ) < |x.toReal| := by -- --- PROOF ---
  have hx : Dyadic.toReal (⟨x.mantissa.natAbs, x.exponent⟩ : Dyadic fmt.p) = |x.toReal| := by
    have h2 : (0 : ℝ) < 2 ^ x.exponent := zpow_pos two_pos _
    rw [Dyadic.toReal_def, toReal_def, abs_mul, abs_of_pos h2, Int.natCast_natAbs, Int.cast_abs]
  have hm : Dyadic.toReal (⟨fmt.maxSignificand, fmt.emax - fmt.p + 1⟩ : Dyadic fmt.p)
      = ((fmt.maxFinite : ℚ) : ℝ) := by
    rw [Dyadic.toReal_def, IEEEFormat.maxFinite]
    push_cast
    rfl
  rw [overflows, Bool.not_eq_true', ← Bool.not_eq_true, Dyadic.le_iff, hx, hm, not_le]

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
