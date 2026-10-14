module

public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# `ContSet/SetIntersection/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- =============================  `SetIntersection.mem_construct`  ============================== --
-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Unfolds membership to a fact about every branch, for every proof below. -/
theorem SetIntersection.mem_construct [ContSet S α] {I : SetIntersection S} {x : α} :
    x ∈ ContSet.construct I ↔ ∀ s ∈ I.sets, x ∈ ContSet.construct s := by
  show x ∈ SetIntersection.construct I ↔ _
  simp [SetIntersection.construct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
