module

public import CORALean.ContSet.WithEmpty.WithEmpty

@[expose] public section

/-!
# `ContSet/WithEmpty/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ===============================  `WithEmpty.construct_empty`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The empty case denotes `∅`. -/
@[simp] theorem WithEmpty.construct_empty [ContSet S α] :
    ContSet.construct (WithEmpty.empty : WithEmpty S) = (∅ : Set α) := rfl


-- =================================  `WithEmpty.construct_of`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A wrapped representation denotes what it denotes. -/
@[simp] theorem WithEmpty.construct_of [ContSet S α] (s : S) :
    ContSet.construct (WithEmpty.of s) = ContSet.construct s := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
