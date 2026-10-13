import CORALean.Global.Float.Instances.Dyadic.Operations.Le
import CORALean.Global.Float.Instances.Dyadic.Operations.LeAligned
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeAlignedIff
import CORALean.Global.Float.Instances.Dyadic.Theorems.LeShlIff

/-!
# Comparison agrees with ℝ

`le` is `leAligned` with the power of two replaced by a sign test where it would dwarf the other
mantissa (`leShl_iff`), and `leAligned_iff` compares aligned integers. Shared by
`toReal_minimum`, `toReal_maximum` and `toReal_le_of_le`, each of which needs both directions or
only the one `SoundFloatArithmetic` asks for.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : Dyadic p) : le a b = true ↔ toReal a ≤ toReal b := by -- --- PROOF ---
  rw [← leAligned_iff, le, leAligned]
  by_cases h : a.exponent ≤ b.exponent
  · rw [if_pos h, leShl_iff, min_eq_left h, decide_eq_true_eq]
    simp
  · rw [if_neg h, leShr, leShl_iff, min_eq_right (le_of_not_ge h), decide_eq_true_eq]
    simp

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
