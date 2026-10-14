module

public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.Specification.Specification
public import CORALean.Specification.Theorems.Basic

@[expose] public section

/-!
# `Specification.holds_custom_iff`

A custom specification holds on `X` exactly when its predicate does: the predicate is downward
closed and closed under unions, so the largest set it admits is the union of all of them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {ContSet α : Type} [CORALean.ContSet ContSet α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_custom_iff (p : Set α → Prop)
    (mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i))
    {X : Set α} : (Specification.custom p mono iUnionClosed).Holds X ↔ p X := by
  rw [Specification.custom, Specification.holds_safeSet, ContSet.construct_set]
  refine ⟨fun hsub => mono hsub (iUnionClosed fun h => h.2), fun hpX => ?_⟩
  exact Set.subset_iUnion (fun h : {S : Set α // p S} => h.1) ⟨X, hpX⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
