module

public import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
public import CORALean.ContSet.Taylm.Real.Theorems.HalveBoxSub

@[expose] public section

/-!
# The optimizer's upper end is attained or exceeded

The cutoff is always some point's upper estimate, a point of a live box inside `X`, so the minimum
over `X` is at most the cutoff, [1, Sec. 4].

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exists_le_globalMin {f : Vec ℝ n → ℝ} {lb : (Fin n → ℝ × ℝ) → ℝ}
    {ub : Vec ℝ n → ℝ} {X : Fin n → ℝ × ℝ} (hub : ∀ p, Taylm.InBox X p → f p ≤ ub p)
    (hX : ∀ k, (X k).1 ≤ (X k).2) (fuel : ℕ) :
    ∃ p, Taylm.InBox X p ∧ f p ≤ (Taylm.globalMin lb ub X fuel).2 := by -- --- PROOF ---
  -- the centre of a proper box lies in it
  have hmid : ∀ B : Fin n → ℝ × ℝ, (∀ k, (B k).1 ≤ (B k).2) → Taylm.InBox B (Taylm.boxMid B) :=
    fun B hB k => by simp only [Taylm.boxMid]; constructor <;> linarith [hB k]
  -- live boxes are proper and inside `X`, and some point of `X` is at most the cutoff
  have inv : ∀ fuel (st : List (Fin n → ℝ × ℝ) × ℝ),
      (∀ B ∈ st.1, (∀ k, (B k).1 ≤ (B k).2) ∧ ∀ t, Taylm.InBox B t → Taylm.InBox X t) →
      (∃ p, Taylm.InBox X p ∧ f p ≤ st.2) →
      ∃ p, Taylm.InBox X p ∧ f p ≤ (Taylm.goLoop lb ub fuel st).2 := by
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
        simp only [Taylm.goLoop, Taylm.goStep]
        split_ifs with hc
        · exact ih _ (fun B' hB' => hl B' (by simp [hB'])) hp
        · split
          · refine ih _ (fun B' hB' => ?_) hcut
            rcases List.mem_append.1 hB' with h | h
            · exact hl B' (by simp [h])
            · simp at h; subst h; exact hBp
          -- bisected: the halves are proper and inside the box
          · rename_i β _
            obtain ⟨h1, h2, h3, h4⟩ := Taylm.halveBox_sub hBp.1 β
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
