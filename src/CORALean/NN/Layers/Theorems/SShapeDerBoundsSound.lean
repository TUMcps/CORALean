module

public import CORALean.NN.Layers.Operations.SShapeDerBounds
public import Mathlib.Algebra.Order.Group.Defs

@[expose] public section

/-!
# The derivative bounds hold

For an S-shaped `df`, every `t ∈ [l, u]` has `df t` between the two bounds. The lower bound is at
the end farther from `0` (by evenness, compared through `-l ≥ u`) and the upper one at `0` or at
the end nearer to it. Outer, a bound, not the exact range: the bounds are attained only at the
ends, and for `l ≤ 0 ≤ u` the lower one is `df` at one end.

## Inputs
* `df` – derivative of the activation
* `l` – lower end of the box
* `u` – upper end of the box
* `t` – point in the box

## Hypotheses
* `h` – the derivative is S-shaped
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* the derivative at the point lies in the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `df t` lies in `[df_l, df_u]` for every `t ∈ [l, u]`. -/
theorem sShapeDerBounds_sound {df : α → α} (h : IsSShape df) {l u t : α} (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    (sShapeDerBounds df l u).inf ≤ df t ∧ df t ≤ (sShapeDerBounds df l u).sup := by -- --- PROOF ---
  -- `df` rises towards `0` on the left, by evenness
  have hneg : ∀ {s t : α}, s ≤ t → t ≤ 0 → df s ≤ df t := fun {s t} hst ht => by
    rw [← h.even s, ← h.even t]
    exact h.anti (neg_nonneg.mpr ht) (neg_le_neg hst)
  unfold sShapeDerBounds
  by_cases h1 : l ≤ 0 ∧ 0 ≤ u
  · -- `0` inside: the peak is `df 0`, the least value at the farther end
    simp only [if_pos h1]
    obtain ⟨hl0, hu0⟩ := h1
    have hup : df t ≤ df 0 := by
      rcases le_total 0 t with ht | ht
      · exact h.anti le_rfl ht
      · exact hneg ht le_rfl
    split_ifs with hc
    · refine ⟨?_, hup⟩
      rcases le_total 0 t with ht | ht
      · rw [← h.even l]
        exact h.anti ht (hu.trans hc)
      · exact hneg hl ht
    · refine ⟨?_, hup⟩
      rcases le_total 0 t with ht | ht
      · exact h.anti ht hu
      · rw [← h.even t]
        exact h.anti (neg_nonneg.mpr ht) (le_trans (neg_le_neg hl) (not_le.mp hc).le)
  · simp only [if_neg h1]
    by_cases h2 : 0 < l
    · -- right of `0`: decreasing
      simp only [if_pos h2]
      have ht : 0 ≤ t := h2.le.trans hl
      exact ⟨h.anti ht hu, h.anti h2.le hl⟩
    · -- left of `0`: increasing
      simp only [if_neg h2]
      have hl0 : l ≤ 0 := not_lt.mp h2
      have hu0 : u ≤ 0 := by
        by_contra hcon
        exact h1 ⟨hl0, (not_le.mp hcon).le⟩
      exact ⟨hneg hl (hu.trans hu0), hneg hu hu0⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
