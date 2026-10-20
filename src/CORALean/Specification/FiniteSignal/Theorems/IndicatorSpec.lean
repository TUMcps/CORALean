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
theorem aux_indicator_finish (dur : ℝ) (L : List ℝ) (W : List Bool) (F : ℝ → Bool)
    (hv : (⟨L, W⟩ : FiniteSignal ℝ Bool).IsValid)
    (hd : (⟨L, W⟩ : FiniteSignal ℝ Bool).duration = dur)
    (hat : ∀ t : ℝ, 0 ≤ t → t ≤ dur → FiniteSignal.valueAt (L.zip W) t = some (F t)) :
    ∃ r, FiniteSignal.mk? L W = some r ∧ r.IsValid ∧ r.duration = dur ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ dur → r.at? t = some (F t) := by -- --- PROOF ---
  refine ⟨⟨L, W⟩, (FiniteSignal.mk?_eq_some_iff _ _ _).mpr ⟨rfl, rfl, hv⟩, hv, hd,
    fun t h0 h1 => ?_⟩
  rw [FiniteSignal.at?_eq_valueAt _ hv.2.1 t, if_pos ⟨h0, hd ▸ h1⟩]
  exact hat t h0 h1


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.indicator?_spec (dur : ℝ) (lo hi : EReal) (val : Bool) (h0 : 0 ≤ dur)
    (hlh : lo < hi) : -- --- CONCL ---
    ∃ r, FiniteSignal.indicator? dur lo hi val = some r ∧ r.IsValid ∧ r.duration = dur ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ dur → r.at? t = some (decide (val = true ∧ (0 : EReal) < hi ∧
        lo < (dur : EReal) ∧ lo ≤ (t : EReal) ∧
          ((t : EReal) < hi ∨ (dur : EReal) ≤ hi))) := by -- --- PROOF ---
  unfold FiniteSignal.indicator?
  rw [if_neg (not_le.mpr hlh)]
  by_cases c1 : val = false ∨ hi ≤ 0 ∨ (dur : EReal) ≤ lo
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
    have hh0' : (0 : EReal) < hi := not_le.mp hh0
    have hld' : lo < (dur : EReal) := not_le.mp hld
    by_cases c2 : lo ≤ 0 ∧ (dur : EReal) ≤ hi
    · -- interval completely covers range
      rw [if_pos c2]
      refine aux_indicator_finish dur [dur] [true] _ ⟨by simp, by simp, by simp, by simp,
        by simpa using h0⟩ (by simp [FiniteSignal.duration]) (fun t ht0 ht1 => ?_)
      have hlt : lo ≤ (t : EReal) := c2.1.trans (by exact_mod_cast ht0)
      simp [FiniteSignal.valueAt_singleton, hh0', hld', hlt, c2.2]
    · rw [if_neg c2]
      by_cases c3 : lo ≤ 0
      · -- interval overlaps left range bound
        rw [if_pos c3]
        have hhd : hi < (dur : EReal) := not_le.mp (fun h => c2 ⟨c3, h⟩)
        obtain ⟨h', rfl⟩ : ∃ h' : ℝ, hi = (h' : EReal) :=
          ⟨hi.toReal, (EReal.coe_toReal (ne_top_of_lt hhd) (ne_bot_of_gt hh0')).symm⟩
        have e1 : 0 < h' := EReal.coe_pos.mp hh0'
        have e2 : h' < dur := EReal.coe_lt_coe_iff.mp hhd
        simp only [EReal.toReal_coe]
        refine aux_indicator_finish dur [h', dur] [true, false] _ ⟨by simp, by simp, by simp [e2],
          by simp, by simp [e1.le, h0]⟩ (by simp [FiniteSignal.duration]) (fun t ht0 ht1 => ?_)
        have hlt : lo ≤ (t : EReal) := c3.trans (by exact_mod_cast ht0)
        have hnd : ¬ (dur : EReal) ≤ (h' : EReal) := not_le.mpr hhd
        by_cases ht : t < h'
        · simp [FiniteSignal.valueAt, ht, hh0', hld', hlt, EReal.coe_lt_coe_iff.mpr ht]
        · simp [FiniteSignal.valueAt, ht, hnd, EReal.coe_lt_coe_iff]
      · -- the interval starts inside the range
        rw [if_neg c3]
        have hl0 : (0 : EReal) < lo := not_le.mp c3
        obtain ⟨l', rfl⟩ : ∃ l' : ℝ, lo = (l' : EReal) :=
          ⟨lo.toReal, (EReal.coe_toReal (ne_top_of_lt hld') (ne_bot_of_gt hl0)).symm⟩
        have e1 : 0 < l' := EReal.coe_pos.mp hl0
        have e2 : l' < dur := EReal.coe_lt_coe_iff.mp hld'
        simp only [EReal.toReal_coe]
        by_cases c4 : (dur : EReal) ≤ hi
        · -- interval overlaps right range bound
          rw [if_pos c4]
          refine aux_indicator_finish dur [l', dur] [false, true] _ ⟨by simp, by simp,
            by simp [e2], by simp, by simp [e1.le, h0]⟩ (by simp [FiniteSignal.duration])
            (fun t ht0 ht1 => ?_)
          by_cases ht : t < l'
          · simp [FiniteSignal.valueAt, ht, EReal.coe_lt_coe_iff, EReal.coe_le_coe_iff]
          · have hlt := not_lt.mp ht
            simp [FiniteSignal.valueAt, ht, c4, hh0', hld', EReal.coe_le_coe_iff, hlt]
        · -- interval is contained in range
          rw [if_neg c4]
          have hhd : hi < (dur : EReal) := not_le.mp c4
          obtain ⟨h', rfl⟩ : ∃ h' : ℝ, hi = (h' : EReal) :=
            ⟨hi.toReal, (EReal.coe_toReal (ne_top_of_lt hhd) (ne_bot_of_gt hh0')).symm⟩
          have e3 : l' < h' := EReal.coe_lt_coe_iff.mp hlh
          have e4 : h' < dur := EReal.coe_lt_coe_iff.mp hhd
          have e5 : 0 < h' := EReal.coe_pos.mp hh0'
          simp only [EReal.toReal_coe]
          refine aux_indicator_finish dur [l', h', dur] [false, true, false] _ ⟨by simp, by simp,
            by simp [e2, e3, e4], by simp, by simp [e1.le, e5.le, h0]⟩
            (by simp [FiniteSignal.duration])
            (fun t ht0 ht1 => ?_)
          by_cases ht : t < l'
          · simp [FiniteSignal.valueAt, ht, EReal.coe_lt_coe_iff, EReal.coe_le_coe_iff]
          · by_cases ht' : t < h'
            · simp [FiniteSignal.valueAt, ht, ht', hh0', hld', c4, EReal.coe_lt_coe_iff,
                EReal.coe_le_coe_iff, not_lt.mp ht]
            · simp [FiniteSignal.valueAt, ht, ht', hh0', hld', c4, EReal.coe_lt_coe_iff,
                EReal.coe_le_coe_iff, not_lt.mp ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
