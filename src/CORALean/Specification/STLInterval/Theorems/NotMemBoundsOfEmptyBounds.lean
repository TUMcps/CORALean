module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Definitions.MemBounds

@[expose] public section

/-!
# An empty interval contains no time

If `isemptyobject(stlInterval(lb,ub,lc,rc))` holds, no time lies in it.

## Inputs
* `T` – time type
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `t` – time

## Hypotheses
* `h` – the bounds describe an empty interval

## Conclusion
* the time does not lie between the bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.not_memBounds_of_emptyBounds {T : Type} [LinearOrder T] (lb : T)
    (ub : WithTop T) (lc rc : Bool) (t : T)
    (h : STLInterval.emptyBounds lb ub lc rc = true) : -- --- CONCL ---
    ¬ STLInterval.memBounds lb ub lc rc t := by -- --- PROOF ---
  -- an empty interval is one whose ends cross, or meet while one is open
  intro hm
  simp only [TimeOrder.isEqvTop_iff_eq, STLInterval.emptyBounds] at h
  split_ifs at h with hc
  obtain ⟨h1, h3⟩ := hm
  have hlt : (lb : WithTop T) ≤ t := by
    rcases h1 with h1 | ⟨-, h1⟩
    · exact WithTop.coe_le_coe.mpr h1.le
    · rw [h1]
  have htu : (t : WithTop T) ≤ ub := by
    rcases h3 with h3 | ⟨-, h3⟩
    · exact h3.le
    · rw [h3]
  -- a time in the interval lies between the ends
  rcases hc with hc | ⟨hc, hc'⟩
  · exact absurd hc (not_lt.mpr (hlt.trans htu))
  · rw [hc] at htu
    have heq : t = lb := le_antisymm (WithTop.coe_le_coe.mp htu) (WithTop.coe_le_coe.mp hlt)
    apply hc'
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | ⟨h1, -⟩
      · exact absurd heq h1.ne'
      · exact h1
    · rcases h3 with h3 | ⟨h3, -⟩
      · rw [hc, heq] at h3; exact absurd h3 (lt_irrefl _)
      · exact h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
