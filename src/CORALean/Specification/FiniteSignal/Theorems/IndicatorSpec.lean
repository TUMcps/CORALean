module

public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Theorems.AtEqValueAt
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkEqSomeIff

@[expose] public section

/-!
# What `indicator` computes

For a non-negative duration and a proper interval, `indicator` returns a valid signal of that
duration that is `val` on the interval and false elsewhere: the right end of the interval is open
(`[lo,hi)`) unless the interval reaches the end of the signal, where the signal is closed. An
interval entirely before `0` or from `dur` on gives the constant false signal.

## Inputs
* `dur` – signal duration
* `lo` – interval lower bound
* `hi` – interval upper bound
* `val` – value on the interval

## Hypotheses
* `h0` – the duration is nonnegative
* `hlh` – the interval is proper

## Conclusion
* a valid signal of that duration that is `val` exactly on the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A signal built from explicit lists: valid, of the given duration, with the given values. -/
private theorem aux_indicator_finish (dur : ℝ) (L : List ℝ) (W : List Bool) (F : ℝ → Bool)
    (hv : (⟨L, W⟩ : FiniteSignal ℝ Bool).IsValid)
    (hd : (⟨L, W⟩ : FiniteSignal ℝ Bool).duration = dur)
    (hat : ∀ t : ℝ, 0 ≤ t → t ≤ dur → FiniteSignal.valueAt (L.zip W) t = some (F t))
    : -- --- CONCL ---
    ∃ r, FiniteSignal.mk? L W = some r ∧ r.IsValid ∧ r.duration = dur ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ dur → r.at? t = some (F t) := by -- --- PROOF ---
  refine ⟨⟨L, W⟩, (FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩, hv, hd,
    fun t h0 h1 => ?_⟩
  rw [FiniteSignal.at?_eq_valueAt _ hv.2.1 t, if_pos ⟨h0, hd ▸ h1⟩]
  exact hat t h0 h1


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.indicator?_spec (dur lo hi : ℝ) (val : Bool) (h0 : 0 ≤ dur)
    (hlh : lo < hi) : -- --- CONCL ---
    ∃ r, FiniteSignal.indicator? dur lo hi val = some r ∧ r.IsValid ∧ r.duration = dur ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ dur → r.at? t = some (decide (val = true ∧ 0 < hi ∧ lo < dur ∧
        lo ≤ t ∧ (t < hi ∨ dur ≤ hi))) := by -- --- PROOF ---
  unfold FiniteSignal.indicator?
  rw [if_neg (not_le.mpr hlh)]
  by_cases c1 : val = false ∨ hi ≤ 0 ∨ dur ≤ lo
  · -- default value or interval out of range
    rw [if_pos c1]
    refine aux_indicator_finish dur [dur] [false] _ ⟨by simp, by simp, by simp, by simp,
      by simpa using h0⟩ (by simp [FiniteSignal.duration]) (fun t ht0 ht1 => ?_)
    simp only [List.zip_cons_cons, List.zip_nil_right, FiniteSignal.valueAt_singleton,
      Option.some.injEq]
    rcases c1 with h | h | h
    · simp [h]
    · simp [not_lt.mpr h]
    · simp [not_lt.mpr h]
  · rw [if_neg c1]
    simp only [not_or] at c1
    obtain ⟨hv1, hh0, hld⟩ := c1
    have hv : val = true := by simpa using hv1
    subst hv
    have hh0' : 0 < hi := not_le.mp hh0
    have hld' : lo < dur := not_le.mp hld
    by_cases c2 : lo ≤ 0 ∧ dur ≤ hi
    · -- interval completely covers range
      rw [if_pos c2]
      refine aux_indicator_finish dur [dur] [true] _ ⟨by simp, by simp, by simp, by simp,
        by simpa using h0⟩ (by simp [FiniteSignal.duration]) (fun t ht0 ht1 => ?_)
      have hlt : lo ≤ t := c2.1.trans ht0
      simp [FiniteSignal.valueAt_singleton, hh0', hld', hlt, c2.2]
    · rw [if_neg c2]
      by_cases c3 : lo ≤ 0
      · -- interval overlaps left range bound
        rw [if_pos c3]
        have hhd : hi < dur := not_le.mp (fun h => c2 ⟨c3, h⟩)
        refine aux_indicator_finish dur [hi, dur] [true, false] _ ⟨by simp, by simp,
          by simp [hhd], by simp, by simp [hh0'.le, h0]⟩ (by simp [FiniteSignal.duration])
          (fun t ht0 ht1 => ?_)
        have hlt : lo ≤ t := c3.trans ht0
        have hnd : ¬ dur ≤ hi := not_le.mpr hhd
        by_cases ht : t < hi
        · simp [FiniteSignal.valueAt, ht, hh0', hld', hlt]
        · simp [FiniteSignal.valueAt, ht, hnd]
      · -- the interval starts inside the range
        rw [if_neg c3]
        have hl0 : 0 < lo := not_le.mp c3
        by_cases c4 : dur ≤ hi
        · -- interval overlaps right range bound
          rw [if_pos c4]
          refine aux_indicator_finish dur [lo, dur] [false, true] _ ⟨by simp, by simp,
            by simp [hld'], by simp, by simp [hl0.le, h0]⟩ (by simp [FiniteSignal.duration])
            (fun t ht0 ht1 => ?_)
          by_cases ht : t < lo
          · simp [FiniteSignal.valueAt, ht, not_le.mpr ht]
          · have hlt := not_lt.mp ht
            simp [FiniteSignal.valueAt, ht, c4, hh0', hld', hlt]
        · -- interval is contained in range
          rw [if_neg c4]
          have hhd : hi < dur := not_le.mp c4
          refine aux_indicator_finish dur [lo, hi, dur] [false, true, false] _ ⟨by simp, by simp,
            by simp [hld', hlh, hhd], by simp, by simp [hl0.le, hh0'.le, h0]⟩
            (by simp [FiniteSignal.duration])
            (fun t ht0 ht1 => ?_)
          by_cases ht : t < lo
          · simp [FiniteSignal.valueAt, ht, not_le.mpr ht]
          · by_cases ht' : t < hi
            · simp [FiniteSignal.valueAt, ht, ht', hh0', hld', c4, not_lt.mp ht]
            · simp [FiniteSignal.valueAt, ht, ht', hh0', hld', c4, not_lt.mp ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
