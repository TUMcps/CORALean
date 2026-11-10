module

public import CORALean.ContSet.OptEmpty.OptEmpty

@[expose] public section

/-!
# `ContSet/OptEmpty/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ==================================  `OptEmpty.toSet_empty`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The empty case denotes `∅`. -/
@[simp] theorem OptEmpty.toSet_empty [ContSet S α] :
    ContSet.toSet (OptEmpty.empty : OptEmpty S) = (∅ : Set α) := rfl


-- ===================================  `OptEmpty.toSet_of`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A wrapped representation denotes what it denotes. -/
@[simp] theorem OptEmpty.toSet_of [ContSet S α] (s : S) :
    ContSet.toSet (OptEmpty.of s) = ContSet.toSet s := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
