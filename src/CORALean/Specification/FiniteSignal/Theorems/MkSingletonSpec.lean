module

public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The constant signal

`finiteSignal(dur,v)` is the signal that is `v` on all of `[0,dur]`: the constructor fails for a
negative `dur`, otherwise the signal is valid, lasts `dur` and is `v` at every time of `[0,dur]`.

## Inputs
* `V` – value type
* `dur` – signal duration
* `v` – constant value

## Hypotheses
* none

## Conclusion
* fails for negative duration, else a valid signal constantly `v`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.mk?_singleton_spec {V : Type} [DecidableEq V] (dur : ℝ) (v : V) :
    (dur < 0 → FiniteSignal.mk? [dur] [v] = none) ∧
    (0 ≤ dur → ∃ s, FiniteSignal.mk? [dur] [v] = some s ∧ s.IsValid ∧ s.duration = dur ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ dur → s.at? t = some v) := by -- --- PROOF ---
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · -- a negative duration fails the constructor
    by_contra h
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨h1, -, hvalid⟩ := (FiniteSignal.mk?_eq_some_iff _ _ _).mp hs
    have := hvalid.2.2.2.2 dur (by rw [h1]; simp)
    exact absurd this (not_le.mpr hd)
  · -- otherwise the signal is the constant one
    have hv : (⟨[dur], [v]⟩ : FiniteSignal ℝ V).IsValid := by simp [FiniteSignal.IsValid, hd]
    refine ⟨⟨[dur], [v]⟩, (FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩, hv,
      by simp [FiniteSignal.duration], fun t h0 h1 => ?_⟩
    rw [FiniteSignal.at?_eq_valueAt _ rfl t,
      if_pos ⟨h0, by simpa [FiniteSignal.duration] using h1⟩]
    simp [FiniteSignal.pairs, FiniteSignal.valueAt_singleton]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
