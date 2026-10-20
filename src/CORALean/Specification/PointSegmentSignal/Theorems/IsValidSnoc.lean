module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Appending a point keeps a signal valid

Appending a point above all earlier ones keeps a valid signal valid, unless the point repeats the
interval before and after it. To an empty signal only the point `0` can be appended.

## Inputs
* `tp` – time points
* `val` – stored values
* `τ` – appended time point
* `pv` – point value of the new point
* `iv` – interval value after the new point

## Hypotheses
* `h` – the signal is empty or valid with the new point not redundant

## Conclusion
* the extended signal is valid
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Appending a non-redundant larger point keeps a signal valid. -/
theorem PointSegmentSignal.isValid_snoc (tp : List T) (val : List Bool) (τ : T) (pv iv : Bool) (h
    : (tp = [] ∧ val = [] ∧ τ = 0) ∨ ((PointSegmentSignal.mk tp val).IsValid ∧ (∀ x ∈ tp, x < τ) ∧
    ¬ (pv = val.getD (val.length - 1) false ∧ pv = iv))) :
    (PointSegmentSignal.mk (tp ++ [τ]) (val ++ [pv, iv])).IsValid := by -- --- PROOF ---
  -- the empty start, or a valid output extended by a larger point
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨⟨hne, hlen, hhead, hsort, hnr⟩, hlt, hnew⟩
  · refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro i hi hi'; simp at hi'; omega
  · dsimp only at hne hlen hhead hsort hnr
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · simp [hlen]; omega
    · rw [List.head?_append, hhead]; rfl
    · exact List.pairwise_append.mpr ⟨hsort, by simp, by simpa using hlt⟩
    · intro i hi hi'
      simp only [List.length_append, List.length_singleton] at hi'
      -- a point of the output is an old one or the new one
      have hpos : 0 < tp.length := List.length_pos_iff.mpr hne
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt' | heq
      · simp only
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
          List.getD_append _ _ _ _ (by omega)]
        exact hnr i hi hlt'
      -- the new point: the point before it ends in the last value
      · subst heq
        simp only
        have e1 : (val ++ [pv, iv]).getD (2 * tp.length) false = pv := by
          rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hlen]
        have e2 : (val ++ [pv, iv]).getD (2 * tp.length + 1) false = iv := by
          rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hlen]
        rw [e1, e2, List.getD_append _ _ _ _ (by omega),
          show 2 * tp.length - 1 = val.length - 1 by omega]
        exact fun hc => hnew ⟨hc.2, hc.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
