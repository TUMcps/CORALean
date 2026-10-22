module

public import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The optimizer's upper end is attained or exceeded

The cutoff is always some point's upper estimate, a point of a live box inside `X`, so the minimum
over `X` is at most the cutoff, [1, Sec. 4].

## Inputs
* `f` – enclosed function
* `lb` – lower bounding function
* `ub` – upper bounding function
* `X` – domain box
* `fuel` – step budget

## Hypotheses
* `hub` – the upper bounding function dominates the function on the box
* `hX` – the box ends are ordered

## Conclusion
* some point of the box has a value below the upper end

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The halves of a proper box are proper boxes inside it. -/
theorem Taylm.aux_halveBox_sub {B : Fin n → Interval ℝ} (hB : ∀ k, (B k).inf ≤ (B k).sup)
    (β : Fin n) : -- --- CONCL ---
    (∀ k, ((Taylm.halveBox B β).1 k).inf ≤ ((Taylm.halveBox B β).1 k).sup) ∧
      (∀ k, ((Taylm.halveBox B β).2 k).inf ≤ ((Taylm.halveBox B β).2 k).sup) ∧
      (∀ t, Taylm.InBox (Taylm.halveBox B β).1 t → Taylm.InBox B t) ∧
      (∀ t, Taylm.InBox (Taylm.halveBox B β).2 t → Taylm.InBox B t) := by -- --- PROOF ---
  have hm := hB β
  refine ⟨fun k => ?_, fun k => ?_, fun t ht k => ?_, fun t ht k => ?_⟩
  -- coordinate `β` is halved, the others are kept
  · simp only [Taylm.halveBox, Function.update_apply]; split_ifs with hk
    · subst hk; simp only; linarith
    · exact hB k
  · simp only [Taylm.halveBox, Function.update_apply]; split_ifs with hk
    · subst hk; simp only; linarith
    · exact hB k
  · have := ht k
    simp only [Taylm.halveBox, Function.update_apply] at this; split_ifs at this with hk
    · subst hk; exact ⟨this.1, by linarith [this.2]⟩
    · exact this
  · have := ht k
    simp only [Taylm.halveBox, Function.update_apply] at this; split_ifs at this with hk
    · subst hk; exact ⟨by linarith [this.1], this.2⟩
    · exact this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exists_le_globalMin {f : Vec ℝ n → ℝ} {lb : (Fin n → Interval ℝ) → ℝ}
    {ub : Vec ℝ n → ℝ} {X : Fin n → Interval ℝ} (hub : ∀ p, Taylm.InBox X p → f p ≤ ub p)
    (hX : ∀ k, (X k).inf ≤ (X k).sup) (fuel : ℕ) : -- --- CONCL ---
    ∃ p, Taylm.InBox X p ∧ f p ≤ (Taylm.globalMin lb ub X fuel).sup := by -- --- PROOF ---
  -- the center of a proper box lies in it
  have hmid : ∀ B : Fin n → Interval ℝ, (∀ k, (B k).inf ≤ (B k).sup) →
      Taylm.InBox B (Taylm.boxMid B) :=
    fun B hB k => by simp only [Taylm.boxMid]; constructor <;> linarith [hB k]
  -- live boxes are proper and inside `X`, and some point of `X` is at most the cutoff
  have inv : ∀ fuel (st : List (Fin n → Interval ℝ) × ℝ),
      (∀ B ∈ st.1, (∀ k, (B k).inf ≤ (B k).sup) ∧ ∀ t, Taylm.InBox B t → Taylm.InBox X t) →
      (∃ p, Taylm.InBox X p ∧ f p ≤ st.2) →
      ∃ p, Taylm.InBox X p ∧ f p ≤ (Taylm.aux_goLoop lb ub fuel st).2 := by
    intro fuel
    -- by induction over the box steps
    induction fuel with
    | zero => intro st _ h; exact h
    | succ k ih =>
      intro st hl hp
      obtain ⟨l, cut⟩ := st
      cases l with
      | nil => exact ih _ hl hp
      | cons B rest =>
        have hBp := hl B (by simp)
        -- the new cutoff is still above a point of `X`
        have hcut : ∃ p, Taylm.InBox X p ∧ f p ≤ min cut (ub (Taylm.boxMid B)) := by
          obtain ⟨p, hpX, hfp⟩ := hp
          rcases le_total cut (ub (Taylm.boxMid B)) with hc | hc
          · exact ⟨p, hpX, by rw [min_eq_left hc]; exact hfp⟩
          · exact ⟨Taylm.boxMid B, hBp.2 _ (hmid B hBp.1),
              by rw [min_eq_right hc]; exact hub _ (hBp.2 _ (hmid B hBp.1))⟩
        simp only [Taylm.aux_goLoop, Taylm.aux_goStep]
        split_ifs with hc
        · exact ih _ (fun B' hB' => hl B' (by simp [hB'])) hp
        · split
          · refine ih _ (fun B' hB' => ?_) hcut
            rcases List.mem_append.1 hB' with h | h
            · exact hl B' (by simp [h])
            · simp at h; subst h; exact hBp
          -- bisected: the halves are proper and inside the box
          · rename_i β _
            obtain ⟨h1, h2, h3, h4⟩ := Taylm.aux_halveBox_sub hBp.1 β
            refine ih _ (fun B' hB' => ?_) hcut
            rcases List.mem_append.1 hB' with h | h
            · exact hl B' (by simp [h])
            · simp at h
              rcases h with rfl | rfl
              · exact ⟨h1, fun t ht => hBp.2 t (h3 t ht)⟩
              · exact ⟨h2, fun t ht => hBp.2 t (h4 t ht)⟩
  exact inv fuel _ (fun B hB => by simp at hB; subst hB; exact ⟨hX, fun t ht => ht⟩)
    ⟨Taylm.boxMid X, hmid X hX, hub _ (hmid X hX)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
