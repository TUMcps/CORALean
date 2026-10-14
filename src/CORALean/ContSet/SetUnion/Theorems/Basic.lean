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


-- =================================  `SetUnion.mem_construct`  ================================= --
-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Unfolds membership to a witnessing branch, for every proof below. -/
theorem SetUnion.mem_construct [ContSet S α] {u : SetUnion S} {x : α} :
    x ∈ ContSet.construct u ↔ ∃ s ∈ u.sets, x ∈ ContSet.construct s := by
  show x ∈ SetUnion.construct u ↔ _
  simp [SetUnion.construct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
