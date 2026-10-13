import CORALean.ContSet.ConPolyZono.Real.Operations.SplitDepFactor
import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetConstruct

/-!
# The halves of `splitDepFactor` cover the set, exactly

The union of the two halves is the original set: the constraints and the independent block go
unchanged into both, and only the domain of factor `r` is cut at `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.splitDepFactor_union (cPZ : ConPolyZono α) (r : Fin cPZ.p) :
    (cPZ.splitDepFactor r).1.construct ∪ (cPZ.splitDepFactor r).2.construct
      = cPZ.construct := by -- --- PROOF ---
  simp only [ConPolyZono.splitDepFactor]
  rw [ConPolyZono.getSubset_construct _ _ _ _ (by norm_num),
    ConPolyZono.getSubset_construct _ _ _ _ (by norm_num)]
  ext x
  constructor
  · -- either half's factor vector is in the unit cube
    rintro (⟨a, β, h1, h2, hβ, hsat, hx⟩ | ⟨a, β, h1, h2, hβ, hsat, hx⟩) <;>
      refine ⟨a, β, fun k => ?_, hβ, hsat, hx⟩ <;>
      rcases eq_or_ne k r with rfl | hk <;> try exact h2 k hk
    · rw [abs_le] at h1 ⊢; constructor <;> linarith [h1.1, h1.2]
    · rw [abs_le] at h1 ⊢; constructor <;> linarith [h1.1, h1.2]
  · -- a point of the cube lies in the half its `r`-th factor lies in
    rintro ⟨a, β, ha, hβ, hsat, hx⟩
    have hr := ha r
    rw [abs_le] at hr
    rcases le_total (a r) 0 with h0 | h0
    · exact Or.inl ⟨a, β, by rw [abs_le]; constructor <;> linarith [hr.1], fun k _ => ha k, hβ,
        hsat, hx⟩
    · exact Or.inr ⟨a, β, by rw [abs_le]; constructor <;> linarith [hr.2], fun k _ => ha k, hβ,
        hsat, hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
