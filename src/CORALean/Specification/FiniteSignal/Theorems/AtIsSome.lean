module

public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.PairsOfValid
public import CORALean.Specification.FiniteSignal.Theorems.ValueAtConsOfGe

@[expose] public section

/-!
# A signal has a value in its range

For a valid signal, `at(sig,time)` returns a value for every time in `[0, duration]`: it throws
exactly outside.

## Inputs
* `T` – time type
* `V` – value type
* `s` – signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `h0` – the time is nonnegative
* `h1` – the time is within the duration

## Conclusion
* the signal has a value at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonempty list of breakpoints holds a value everywhere. -/
theorem aux_valueAt_isSome {T V : Type} [LinearOrder T] : ∀ (L : List (T × V)) (t : T), L ≠ [] →
    ∃ v, FiniteSignal.valueAt L t = some v
  | [], _, h => absurd rfl h
  | [p], t, _ => ⟨p.2, FiniteSignal.valueAt_singleton p t⟩
  | p :: x :: rest, t, _ => by
    by_cases ht : t < p.1
    · exact ⟨p.2, FiniteSignal.valueAt_cons_of_lt p _ t ht⟩
    · rw [FiniteSignal.valueAt_cons_of_ge p _ t ht (by simp)]
      exact aux_valueAt_isSome (x :: rest) t (by simp)


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.at?_isSome {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hs : s.IsValid) (t : T) (h0 : 0 ≤ t) (h1 : t ≤ s.duration) : ∃ v, s.at? t = some v := by
  obtain ⟨b, v, rest, hq, -, -, -⟩ := FiniteSignal.pairs_of_valid s hs
  rw [FiniteSignal.at?_eq_valueAt s hs.2.1 t, if_pos ⟨h0, h1⟩, hq]
  exact aux_valueAt_isSome _ t (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
