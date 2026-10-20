module

public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.STLInterval.Theorems.RawSetOrdConnected
public import CORALean.Specification.STLInterval.Theorems.SetToLeft
public import CORALean.Specification.STLInterval.Theorems.SetToRight
public import CORALean.Specification.TentativeKleeneSignal.Definitions.IsValid
public import CORALean.Specification.TentativeKleeneSignal.Operations.GetInterval
public import CORALean.Specification.TentativeKleeneSignal.Theorems.SetInvalidSpec
public import CORALean.Specification.TentativeKleeneSignal.Theorems.ToFourValuedSpec

@[expose] public section

/-!
# Reading a tentative signal on an interval

`getInterval(obj,interval)` of a valid signal and an interval from `0` on is valid and, at every
`t ≥ 0`, has the value of the tentative signal inside the interval and `Inconclusive` outside it:
the times to the left and to the right of the interval are made invalid, and every time outside
the interval is one of the two.

## Inputs
* `s` – tentative signal
* `I` – time interval

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* a valid signal equal on the interval and inconclusive outside
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.getInterval_spec (s : TentativeKleeneSignal ℝ) (hs : s.IsValid)
    (I : STLInterval) : -- --- CONCL ---
    (s.getInterval I).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.getInterval I).at t = s.at t) ∧
      (t ∉ I.set → (s.getInterval I).at t = FourValued.ii) := by -- --- PROOF ---
  cases I with
  | empty =>
    -- the empty interval: the inconclusive signal
    obtain ⟨hv, h⟩ := FourValuedSignal.uniformSignal_spec FourValued.ii
    refine ⟨hv, fun t ht => ⟨fun hm => absurd hm (by simp [STLInterval.set]), fun _ => h t ht⟩⟩
  | nonempty l u lc rc a b c z =>
    -- the interval is nonempty, so `toLeft` and `toRight` are the intervals on either side
    have hne : (STLInterval.nonempty l u lc rc a b c z) ≠ .empty := by simp
    obtain ⟨L, hL, hLset⟩ := STLInterval.set_toLeft _ hne
    obtain ⟨R, hR, hRset⟩ := STLInterval.set_toRight _ hne
    simp only [TentativeKleeneSignal.getInterval, hL, hR]
    -- 1. `setInvalid` of the left, then of the right; 2. the four-valued signal of the result
    obtain ⟨v1, g1⟩ := TentativeKleeneSignal.setInvalid_spec s hs L
    obtain ⟨v2, g2⟩ := TentativeKleeneSignal.setInvalid_spec _ v1 R
    obtain ⟨v3, g3⟩ := TentativeKleeneSignal.toFourValued_spec _ ⟨v2.1, v2.2⟩
    refine ⟨v3, fun t ht => ?_⟩
    rw [g3 t ht]
    have hoc := STLInterval.rawSet_ordConnected l u lc rc
    -- inside the interval nothing is made invalid, outside everything is
    constructor
    · intro hm
      have hnL : t ∉ L.set := fun h => by rw [hLset] at h; exact h.2.1 hm
      have hnR : t ∉ R.set := fun h => by rw [hRset] at h; exact h.1 hm
      rw [(g2 t ht).2 hnR, (g1 t ht).2 hnL]
    · intro hm
      -- outside the interval the time is to its left or to its right
      by_cases hmR : t ∈ R.set
      · exact (g2 t ht).1 hmR
      · by_cases hmL : t ∈ L.set
        · rw [(g2 t ht).2 hmR]; exact (g1 t ht).1 hmL
        · exfalso
          rw [hLset] at hmL; rw [hRset] at hmR
          have h1 : ∃ x ∈ (STLInterval.nonempty l u lc rc a b c z).set, x < t := by
            by_contra hcon
            push Not at hcon
            exact hmL ⟨ht, hm, fun x hx => hcon x hx⟩
          have h2 : ∃ y ∈ (STLInterval.nonempty l u lc rc a b c z).set, t < y := by
            by_contra hcon
            push Not at hcon
            exact hmR ⟨hm, fun x hx => hcon x hx⟩
          obtain ⟨x, hx, hxt⟩ := h1
          obtain ⟨y, hy, hty⟩ := h2
          exact hm (hoc.out hx hy ⟨hxt.le, hty.le⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
