module

public import CORALean.Specification.Specification
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# `Specification/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {ContSet α : Type} [CORALean.ContSet ContSet α]


-- =============================  `Specification.holds_invariant`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- An invariant specification holds on `X` when `X` lies in the set. -/
@[simp] theorem Specification.holds_invariant {s : ContSet} {X : Set α} :
    (Specification.invariant s).Holds X ↔ X ⊆ construct s := Iff.rfl


-- ==============================  `Specification.holds_safeSet`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A safe-set specification holds on `X` when `X` lies in the set. -/
@[simp] theorem Specification.holds_safeSet {s : ContSet} {X : Set α} :
    (Specification.safeSet s).Holds X ↔ X ⊆ construct s := Iff.rfl


-- =============================  `Specification.holds_unsafeSet`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- An unsafe-set specification holds on `X` when `X` avoids the set. -/
@[simp] theorem Specification.holds_unsafeSet {s : ContSet} {X : Set α} :
    (Specification.unsafeSet s).Holds X ↔ Disjoint X (construct s) := Iff.rfl

end CORALean


namespace CORALean

variable {ContSet α : Type} [CORALean.ContSet ContSet α] {X O : Set α}


-- ============================  `Specification.holdsAll_of_outer`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Split out of `HoldsOfOuter.lean` (issue #62): the same transfer, one
specification at a time, for `Specification.HoldsAll`. -/
theorem Specification.holdsAll_of_outer (specs : List (Specification ContSet)) (h : X ⊆ O)
    (hO : Specification.HoldsAll specs O) : Specification.HoldsAll specs X :=
  fun spec hmem => (spec.holds_of_outer h) (hO spec hmem)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
