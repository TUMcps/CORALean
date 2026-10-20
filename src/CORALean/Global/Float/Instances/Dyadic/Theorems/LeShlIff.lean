module

public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl

@[expose] public section

/-!
# `leShl` decides `m ≤ n * 2 ^ g`

Past the bit length of `m`, `|n| * 2 ^ g` exceeds `|m|`, so `m ≤ n * 2 ^ g` is `0 < n`; below
it, `leShl` compares directly.

## Inputs
* `m` – integer mantissa
* `n` – integer factor
* `g` – shift

## Hypotheses
* none

## Conclusion
* the shifted comparison is true exactly when the inequality holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem leShl_iff (m n : ℤ) (g : ℕ) :
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

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
