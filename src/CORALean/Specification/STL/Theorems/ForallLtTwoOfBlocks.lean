module

public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# A predicate on `(0,2)` in three blocks

If `P` holds on `(0,1)`, at `1` and on `(1,2)`, written `P (u + 1)` for `u ∈ (0,1)`, it holds on
all of `(0,2)`. How [1, Table 1] reads a window `(0,1)` followed by `X₁` of one.

## Inputs
* `P` – property of times

## Hypotheses
* `hG` – the property holds on the open first block
* `h₁` – the property holds at one
* `hG'` – the property holds on the open second block

## Conclusion
* the property holds on the open interval to two

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem Time.forall_lt_two_of_blocks (P : ℝ≥0 → Prop) (hG : ∀ u, 0 < u → u < 1 → P u) (h₁ : P 1)
    (hG' : ∀ u, 0 < u → u < 1 → P (u + 1)) : ∀ p, 0 < p → p < 2 → P p := by -- --- PROOF ---
  intro p hp₀ hp₂
  rcases lt_trichotomy p 1 with hp | rfl | hp
  · exact hG p hp₀ hp
  · exact h₁
  · -- past `1`, the remainder is a positive number below `1`
    obtain ⟨e, rfl⟩ := exists_add_of_le hp.le
    have he₀ : 0 < e := by simpa using hp
    have he₁ : e < 1 := lt_of_add_lt_add_left (a := 1) (by rw [one_add_one_eq_two]; exact hp₂)
    rw [add_comm]; exact hG' e he₀ he₁

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
