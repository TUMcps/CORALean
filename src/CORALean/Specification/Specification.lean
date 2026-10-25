module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# What a computed set is checked against

CORA's `specification`: a set, stored as any representation, with what it means. A safe set is one
every point must lie in, an unsafe set one no point may lie in; an invariant is checked as a safe
set (`check.m` and `robustness.m` run the same test), so `Holds` is one match. Only the
specification's set is a representation; what it is checked on stays a `Set α`, and
`Theorems.HoldsOfOuter` carries a verdict on an outer approximation. `custom` is not a fourth kind:
it provably survives an outer approximation, pinned down to a safe set. `logic` is out of scope:
satisfying one is model checking.

## References

None: CORA's `specification`, a software class: no publication introduces it, and the CORA manual
page for it could not be read.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- The kind of a specification: a safe set, an unsafe set, or an invariant. -/
inductive Specification.Kind
  | safeSet
  | unsafeSet
  | invariant

/-- `ContSet` is the representation the set is stored in, any type with
`ContSet ContSet α`; at `Set α` it is a plain set. -/
structure Specification (ContSet : Type) where
  set : ContSet
  kind : Specification.Kind

variable {ContSet α : Type} [CORALean.ContSet ContSet α]

/-- Membership required of every point, or of none. -/
def Specification.Holds (spec : Specification ContSet) (X : Set α) : Prop :=
  match spec.kind with
  | .safeSet => X ⊆ construct spec.set
  | .unsafeSet => Disjoint X (construct spec.set)
  | .invariant => X ⊆ construct spec.set

/-- The specification that every point lies in the set `s`. -/
def Specification.safeSet (s : ContSet) : Specification ContSet := ⟨s, .safeSet⟩

/-- The specification that no point lies in the set `s`. -/
def Specification.unsafeSet (s : ContSet) : Specification ContSet := ⟨s, .unsafeSet⟩

/-- CORA's `'invariant'` type: checked as `contains(set, S)`, the same test as
`safeSet` — see `check.m`'s numeric branch and `robustness.m`. -/
def Specification.invariant (s : ContSet) : Specification ContSet := ⟨s, .invariant⟩

/-- A requirement is normally several of these at once, all stored alike. -/
def Specification.HoldsAll (specs : List (Specification ContSet)) (X : Set α) : Prop :=
  ∀ spec ∈ specs, spec.Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
