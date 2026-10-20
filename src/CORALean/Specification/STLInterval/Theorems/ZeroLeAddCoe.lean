module

public import CORALean.Specification.STLInterval.STLInterval
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# A shifted lower bound stays nonnegative

The lower bound of an `stlInterval` is a real number, so shifting it by a real `δ` whose real
sum stays nonnegative keeps the `EReal` sum nonnegative: what `plus` with a number or an interval
needs of `stlInterval(lb,ub,lc,rc)`'s check `lb ≥ 0`.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `δ` – real shift

## Hypotheses
* `hu` – an infinite upper bound is open
* `hlt` – the bounds leave a time in the interval
* `hz` – the lower bound is nonnegative
* `h` – the shifted finite bound is nonnegative

## Conclusion
* the shifted lower bound is nonnegative
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A lower bound `l ≥ 0` of an interval, shifted by a real `δ` with `0 ≤ l.toReal + δ`, is
still `≥ 0`: the bound is finite, since an infinite one is open and so below the upper one. -/
theorem STLInterval.zero_le_add_coe {l u : EReal} {lc rc : Bool} (hu : u = ⊤ → rc = false)
    (hlt : l < u ∨ (l = u ∧ lc = true ∧ rc = true)) (hz : 0 ≤ l) (δ : ℝ)
    (h : 0 ≤ l.toReal + δ) : 0 ≤ l + (δ : EReal) := by -- --- PROOF ---
  have hl : l ≠ ⊤ := by
    rintro rfl
    rcases hlt with h' | ⟨h', -, h''⟩
    · exact absurd h' not_top_lt
    · simp [hu h'.symm] at h''
  have hb : l ≠ ⊥ := by
    rintro rfl
    simp at hz
  lift l to ℝ using ⟨hl, hb⟩
  exact_mod_cast h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
