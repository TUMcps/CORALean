module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitDepFactor
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

@[expose] public section

/-!
# The halves of `splitDepFactor` cover the set, exactly

The union of the two halves is the original set. The independent block is carried unchanged
into both halves, so the statement holds with it: only the factor domain is split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `getSubset` is a point of `pZ` at the substituted factor, the independent block
kept. -/
theorem PolyZonotope.aux_mem_getSubset (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (x : α) : -- --- CONCL ---
    x ∈ (pZ.getSubset k cen rad).construct ↔
      ∃ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ), (∀ k', |a k'| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ x = pZ.point (Function.update a k (cen + rad * a k))
          + ∑ j, β j • pZ.GI j := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, congrArg (· + ∑ j, β j • pZ.GI j)
      (PolyZonotope.getSubset_point pZ k cen rad a)⟩
  · rintro ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (congrArg (· + ∑ j, β j • pZ.GI j)
      (PolyZonotope.getSubset_point pZ k cen rad a)).symm⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitDepFactor_union (pZ : PolyZonotope α) (k : Fin pZ.p) :
    (pZ.splitDepFactor k).1.construct ∪ (pZ.splitDepFactor k).2.construct
      = pZ.construct := by -- --- PROOF ---
  simp only [PolyZonotope.splitDepFactor]
  ext x
  rw [Set.mem_union, PolyZonotope.aux_mem_getSubset, PolyZonotope.aux_mem_getSubset]
  constructor
  · -- a half's point is the original's at the substituted factor, which stays in the cube
    rintro (⟨a, β, ha, hβ, rfl⟩ | ⟨a, β, ha, hβ, rfl⟩)
    · refine ⟨_, β, fun k' => ?_, hβ, rfl⟩
      rcases eq_or_ne k' k with rfl | hk
      · rw [Function.update_self]; have := ha k'; rw [abs_le] at this ⊢; constructor <;> linarith
      · rw [Function.update_of_ne hk]; exact ha k'
    · refine ⟨_, β, fun k' => ?_, hβ, rfl⟩
      rcases eq_or_ne k' k with rfl | hk
      · rw [Function.update_self]; have := ha k'; rw [abs_le] at this ⊢; constructor <;> linarith
      · rw [Function.update_of_ne hk]; exact ha k'
  · -- a point of the cube lies in the half its `k`-th factor lies in
    rintro ⟨a, β, ha, hβ, rfl⟩
    have hk := ha k
    rw [abs_le] at hk
    rcases le_total (a k) 0 with h0 | h0
    · refine Or.inl ⟨Function.update a k (2 * a k + 1), β, fun k' => ?_, hβ, ?_⟩
      · rcases eq_or_ne k' k with rfl | hne
        · rw [Function.update_self, abs_le]; constructor <;> linarith
        · rw [Function.update_of_ne hne]; exact ha k'
      · -- substituting back recovers the original factor vector
        rw [show Function.update (Function.update a k (2 * a k + 1)) k
            (-(2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Function.update a k (2 * a k + 1) k) = a from by
          funext k'
          rcases eq_or_ne k' k with rfl | hne
          · simp; ring
          · simp [hne]]
        rfl
    · refine Or.inr ⟨Function.update a k (2 * a k - 1), β, fun k' => ?_, hβ, ?_⟩
      · rcases eq_or_ne k' k with rfl | hne
        · rw [Function.update_self, abs_le]; constructor <;> linarith
        · rw [Function.update_of_ne hne]; exact ha k'
      · -- substituting back recovers the original factor vector
        rw [show Function.update (Function.update a k (2 * a k - 1)) k
            ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Function.update a k (2 * a k - 1) k) = a from by
          funext k'
          rcases eq_or_ne k' k with rfl | hne
          · simp; ring
          · simp [hne]]
        rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
