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

section

open ContSetLike

variable {ContSet α : Type} [ContSetLike ContSet α]


-- =============================  `Specification.holds_invariant`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- An invariant specification holds on `𝒳` when `𝒳` lies in the set. -/
@[simp] theorem Specification.holds_invariant {S : ContSet} {𝒳 : Set α} :
    (Specification.invariant S).Holds 𝒳 ↔ 𝒳 ⊆ toSet S := Iff.rfl


-- ==============================  `Specification.holds_safeSet`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A safe-set specification holds on `𝒳` when `𝒳` lies in the set. -/
@[simp] theorem Specification.holds_safeSet {S : ContSet} {𝒳 : Set α} :
    (Specification.safeSet S).Holds 𝒳 ↔ 𝒳 ⊆ toSet S := Iff.rfl


-- =============================  `Specification.holds_unsafeSet`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- An unsafe-set specification holds on `𝒳` when `𝒳` avoids the set. -/
@[simp] theorem Specification.holds_unsafeSet {S : ContSet} {𝒳 : Set α} :
    (Specification.unsafeSet S).Holds 𝒳 ↔ Disjoint 𝒳 (toSet S) := Iff.rfl

end


section

variable {ContSet α : Type} [ContSetLike ContSet α] {𝒳 O : Set α}


-- ============================  `Specification.holdsAll_of_outer`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- Split out of `HoldsOfOuter.lean` (issue #62): the same transfer, one
specification at a time, for `Specification.HoldsAll`. -/
theorem Specification.holdsAll_of_outer (specs : List (Specification ContSet)) (h : 𝒳 ⊆ O)
    (hO : Specification.HoldsAll specs O) : Specification.HoldsAll specs 𝒳 :=
  fun spec hmem => (spec.holds_of_outer h) (hO spec hmem)

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
