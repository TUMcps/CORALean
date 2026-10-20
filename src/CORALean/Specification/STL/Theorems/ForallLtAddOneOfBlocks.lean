module

public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# A predicate on three blocks of time

The step every row of [1, Table 1] that nests a window `(0,1)` inside `X₁` takes. If `P` holds
on `(0,1)`, at `1`, on `(1,2)`, and from `1 + s` on for `s ∈ (0,1)` up to `t + 1 + s`, it holds
on `[s, t + 1 + s)`: the offset `t'` is below `1` and `t' + s` lands in one of the first three
blocks, or at least `1` and is one of the shifted ones.

## Inputs
* `P` – property of times
* `s` – offset
* `t` – bound

## Hypotheses
* `hs₀` – the offset is positive
* `hs₁` – the offset is below one
* `hG` – the property holds on the open first block
* `h₁` – the property holds at one
* `hG'` – the property holds on the open second block
* `ht` – the property holds on the shifted third block

## Conclusion
* the property holds on the shifted times below the bound

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

theorem Time.forall_lt_add_one_of_blocks (P : ℝ≥0 → Prop) {s t : ℝ≥0} (hs₀ : 0 < s)
    (hs₁ : s < 1) (hG : ∀ u, 0 < u → u < 1 → P u) (h₁ : P 1)
    (hG' : ∀ u, 0 < u → u < 1 → P (u + 1)) (ht : ∀ u < t, P (u + (s + 1))) :
    ∀ t' < t + 1, P (t' + s) := by -- --- PROOF ---
  intro t' ht'
  rcases le_or_gt 1 t' with h1 | h1
  · -- the offset is at least `1`, so it is one of the shifted ones
    obtain ⟨d, rfl⟩ := exists_add_of_le h1
    have hd : d < t := lt_of_add_lt_add_left (by rwa [add_comm t 1] at ht')
    have e : 1 + d + s = d + (s + 1) := by ring
    rw [e]; exact ht d hd
  · -- below `1`, split on where `t' + s` falls relative to `1`
    rcases lt_trichotomy (t' + s) 1 with hp | hp | hp
    · exact hG _ (lt_of_lt_of_le hs₀ le_add_self) hp
    · rw [hp]; exact h₁
    · obtain ⟨e, he⟩ := exists_add_of_le hp.le
      have he₀ : 0 < e := by
        rcases eq_zero_or_pos e with rfl | h
        · simp at he; rw [he] at hp; exact absurd hp (lt_irrefl _)
        · exact h
      -- `t' + s < 2`, so the part past `1` is again below `1`
      have he₁ : e < 1 := lt_of_add_lt_add_left (by
        calc 1 + e = t' + s := he.symm
          _ < 1 + 1 := add_lt_add h1 hs₁)
      have := hG' e he₀ he₁
      rwa [add_comm e 1, ← he] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
