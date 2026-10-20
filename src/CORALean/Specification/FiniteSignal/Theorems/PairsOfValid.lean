module

public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Basic

@[expose] public section

/-!
# The breakpoints of a valid signal

A valid signal has a first breakpoint `(b,v)` at a non-negative time, followed by the others, and
its breakpoints' times are the times of the signal.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the breakpoints start at a nonnegative time and list the signal's times and values
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.pairs_of_valid {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) : ∃ b v rest, s.pairs = (b, v) :: rest ∧
      s.pairs.map Prod.fst = s.time ∧ s.pairs.map Prod.snd = s.value ∧ 0 ≤ b := by -- --- PROOF ---
  obtain ⟨hne, hl, -, -, hnn⟩ := hs
  have hmap : s.pairs.map Prod.fst = s.time := by simp [FiniteSignal.pairs, List.map_fst_zip, hl]
  have hmaps : s.pairs.map Prod.snd = s.value := by simp [FiniteSignal.pairs, List.map_snd_zip, hl]
  cases hq : s.pairs with
  | nil => exact absurd (by rw [← hmap, hq]; rfl) hne
  | cons p ps =>
    rw [hq] at hmap hmaps
    exact ⟨p.1, p.2, ps, rfl, hmap, hmaps, hnn _ (hmap ▸ List.mem_map_of_mem (List.mem_cons_self))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
