module

public import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
public import CORALean.ContSet.Taylm.Real.Theorems.HalveBoxCover
public import CORALean.ContSet.Taylm.Real.Theorems.ListMinLe

@[expose] public section

/-!
# The optimizer's lower end is a lower bound

[1, Sec. 4]'s elimination is sound: a point of `X` stays in a live box, or its box was eliminated
with a lower bound above the cutoff of the time, which only decreases. For any bounder sound on the
boxes of a class that halving keeps.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.globalMin_le {f : Vec ℝ n → ℝ} {lb : (Fin n → Interval ℝ) → ℝ} {ub : Vec ℝ n → ℝ}
    {Good : (Fin n → Interval ℝ) → Prop}
    (hgood : ∀ B β, Good B → Good (Taylm.halveBox B β).1 ∧ Good (Taylm.halveBox B β).2)
    (hlb : ∀ B, Good B → ∀ t, Taylm.InBox B t → lb B ≤ f t) {X : Fin n → Interval ℝ} (hX : Good X)
    (fuel : ℕ) {t : Vec ℝ n} (ht : Taylm.InBox X t) : -- --- CONCL ---
    (Taylm.globalMin lb ub X fuel).inf ≤ f t := by -- --- PROOF ---
  -- every point is in a live box, or above the cutoff; every live box is good
  have inv : ∀ fuel (st : List (Fin n → Interval ℝ) × ℝ), (∀ B ∈ st.1, Good B) →
      ((∃ B ∈ st.1, Taylm.InBox B t) ∨ st.2 < f t) →
      ((∃ B ∈ (Taylm.aux_goLoop lb ub fuel st).1, Taylm.InBox B t) ∨
        (Taylm.aux_goLoop lb ub fuel st).2 < f t) ∧ ∀ B ∈ (Taylm.aux_goLoop lb ub fuel
          st).1, Good B := by
    intro fuel
    induction fuel with
    | zero => intro st hg h; exact ⟨h, hg⟩
    | succ k ih =>
      intro st hg h
      obtain ⟨l, cut⟩ := st
      cases l with
      | nil => exact ih _ hg h
      | cons B rest =>
        have hB := hg B (by simp)
        simp only [Taylm.aux_goLoop, Taylm.aux_goStep]
        split_ifs with hcut
        -- eliminated: its points are above the cutoff
        · refine ih _ (fun B' hB' => hg B' (by simp [hB'])) ?_
          rcases h with ⟨B', hB', htB'⟩ | hlt
          · rcases List.mem_cons.1 hB' with rfl | hB'
            · exact Or.inr (lt_of_lt_of_le hcut (hlb _ hB _ htB'))
            · exact Or.inl ⟨B', hB', htB'⟩
          · exact Or.inr hlt
        · split
          -- kept whole: the cutoff only decreases
          · refine ih _ (fun B' hB' => ?_) ?_
            · rcases List.mem_append.1 hB' with h' | h'
              · exact hg B' (by simp [h'])
              · simp at h'; subst h'; exact hB
            · rcases h with ⟨B', hB', htB'⟩ | hlt
              · left; refine ⟨B', ?_, htB'⟩
                rcases List.mem_cons.1 hB' with rfl | hB' <;> simp [*]
              · exact Or.inr (lt_of_le_of_lt (min_le_left _ _) hlt)
          -- bisected: the halves cover it and are good
          · rename_i β _
            refine ih _ (fun B' hB' => ?_) ?_
            · rcases List.mem_append.1 hB' with h' | h'
              · exact hg B' (by simp [h'])
              · simp at h'
                rcases h' with rfl | rfl
                · exact (hgood B β hB).1
                · exact (hgood B β hB).2
            · rcases h with ⟨B', hB', htB'⟩ | hlt
              · left
                rcases List.mem_cons.1 hB' with rfl | hB'
                · rcases Taylm.halveBox_cover β htB' with h1 | h2
                  · exact ⟨_, by simp, h1⟩
                  · exact ⟨_, by simp, h2⟩
                · exact ⟨B', by simp [hB'], htB'⟩
              · exact Or.inr (lt_of_le_of_lt (min_le_left _ _) hlt)
  -- from the one box `X`
  obtain ⟨hres, hgd⟩ := inv fuel ([X], ub (Taylm.boxMid X))
    (fun B hB => by simp at hB; subst hB; exact hX)
    (Or.inl ⟨X, by simp, ht⟩)
  rcases hres with ⟨B, hB, htB⟩ | hlt
  · exact le_trans (min_le_right _ _) (le_trans (Taylm.listMin_le lb hB) (hlb B (hgd B hB) t htB))
  · exact le_trans (min_le_left _ _) hlt.le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
