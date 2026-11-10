module

public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# `ContSet/SetUnion/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ===================================  `SetUnion.mem_toSet`  =================================== --
-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Unfolds membership to a witnessing branch, for every proof below. -/
theorem SetUnion.mem_toSet [ContSet S α] {u : SetUnion S} {x : α} :
    x ∈ ContSet.toSet u ↔ ∃ s ∈ u.sets, x ∈ ContSet.toSet s := by
  show x ∈ SetUnion.toSet u ↔ _
  simp [SetUnion.toSet]


-- ================================  `SetUnion.mem_toSet_range`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of step `k < K` lies in the union over the steps, as a run enters a `reach` result. -/
theorem SetUnion.mem_toSet_range [ContSet S α] {f : ℕ → S} {K k : ℕ} (hk : k < K) {x : α}
    (hx : x ∈ ContSet.toSet (f k)) :
    x ∈ ContSet.toSet (⟨(List.range K).map f⟩ : SetUnion S) :=
  SetUnion.mem_toSet.mpr ⟨f k, List.mem_map_of_mem (List.mem_range.mpr hk), hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
