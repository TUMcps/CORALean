module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeAligned
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealAlign
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl

@[expose] public section

/-!
# Comparison agrees with ℝ

`le` is `leAligned` with the power of two replaced by a sign test where it would dwarf the other
mantissa (`aux_leShl_iff`), and `aux_leAligned_iff` compares aligned integers. Shared by
`toReal_minimum`, `toReal_maximum` and `toReal_le_of_le`, each of which needs both directions or
only the one `SoundFloatArithmetic` asks for.

## Inputs
* `a` – left dyadic
* `b` – right dyadic

## Hypotheses
* none

## Conclusion
* the comparison is true exactly when the real order holds
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `leShl` decides `m ≤ n * 2 ^ g`. -/
theorem aux_leShl_iff (m n : ℤ) (g : ℕ) : -- --- CONCL ---
    leShl m n g = true ↔ m ≤ n * 2 ^ g := by -- --- PROOF ---
  unfold leShl
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hn]
  by_cases hg : Nat.log2 m.natAbs < g
  · rw [if_pos hg, decide_eq_true_eq]
    -- the bit length of `m` is below `g`, so `|m| < 2 ^ g ≤ |n| * 2 ^ g`
    have h1 : m.natAbs < 2 ^ g := by
      rcases Nat.eq_zero_or_pos m.natAbs with h | h
      · rw [h]; exact Nat.two_pow_pos g
      · exact (Nat.log2_lt (by omega)).mp hg
    have h2 : (m.natAbs : ℤ) < 2 ^ g := by exact_mod_cast h1
    have h3 : (0 : ℤ) < 2 ^ g := by positivity
    have h4 : -(m.natAbs : ℤ) ≤ m := by omega
    have h5 : m ≤ (m.natAbs : ℤ) := by omega
    rcases lt_or_gt_of_ne hn with hn | hn
    · constructor
      · intro h; omega
      · intro h; nlinarith
    · constructor
      · intro _; nlinarith
      · intro _; exact hn
  · rw [if_neg hg, decide_eq_true_eq]


/-- The aligned comparison agrees with ℝ. -/
theorem aux_leAligned_iff (a b : Dyadic p) : leAligned a b = true ↔ toReal a ≤ toReal b := by
  rw [leAligned, decide_eq_true_eq, toReal_align a (min_le_left a.exponent b.exponent),
    toReal_align b (min_le_right a.exponent b.exponent)]
  exact ⟨fun h => mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _)),
         fun h => Int.cast_le.mp (le_of_mul_le_mul_right h (zpow_pos two_pos _))⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : Dyadic p) : -- --- CONCL ---
    le a b = true ↔ toReal a ≤ toReal b := by -- --- PROOF ---
  rw [← aux_leAligned_iff, le, leAligned]
  by_cases h : a.exponent ≤ b.exponent
  · rw [if_pos h, aux_leShl_iff, min_eq_left h, decide_eq_true_eq]
    simp
  · rw [if_neg h, leShr, aux_leShl_iff, min_eq_right (le_of_not_ge h), decide_eq_true_eq]
    simp

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
