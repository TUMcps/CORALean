module

public import CORALean.Specification.AtomicProposition.Definitions.Holds

@[expose] public section

/-!
# `AtomicProposition/Theorems`: small theorems

One section per theorem, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]


-- ===========================  `AtomicProposition.ofSet_holds_iff`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The proposition `atomicProposition(set)` holds, at every location, exactly in its set. -/
theorem AtomicProposition.ofSet_holds_iff (s : S n) (x : Vec ℝ n) (loc : ℕ) :
    (AtomicProposition.ofSet s).Holds x loc ↔ x ∈ construct s := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  simp [AtomicProposition.ofSet, AtomicProposition.containsLoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
