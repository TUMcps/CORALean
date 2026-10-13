module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# What a computed set is checked against

CORA's `specification`: a set, stored as any representation, together with what it
means. A safe set is one every point must lie in, an unsafe set one no point may lie in,
and an invariant is checked as a safe set is — `check.m` and `robustness.m` run the
identical test for `'safeSet'` and `'invariant'`, differing only in use (a location's
invariant, already `HybridDynamics.Location.inv`, not a goal). Three kinds, two
definitions, why `Holds` is one match.

Only the specification's set is a representation. What it is checked on stays a
`Set α`: the exact image or reachable set has none, and `Theorems.HoldsOfOuter` carries
a verdict on an outer approximation to it. A plain `Set α` is itself a representation
(`construct := id`), which is what `custom` and every set with no data structure use.
`custom` is not a fourth kind: CORA's is an arbitrary function with no guarantee it
survives an outer approximation, so this one provably does, pinned down to a safe set.
`logic`, signal temporal logic, is out of scope: satisfying one is model checking.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

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

def Specification.safeSet (s : ContSet) : Specification ContSet := ⟨s, .safeSet⟩

def Specification.unsafeSet (s : ContSet) : Specification ContSet := ⟨s, .unsafeSet⟩

/-- CORA's `'invariant'` type: checked as `contains(set, S)`, the same test as
`safeSet` — see `check.m`'s numeric branch and `robustness.m`. -/
def Specification.invariant (s : ContSet) : Specification ContSet := ⟨s, .invariant⟩

@[simp] theorem Specification.holds_safeSet {s : ContSet} {X : Set α} :
    (Specification.safeSet s).Holds X ↔ X ⊆ construct s := Iff.rfl

@[simp] theorem Specification.holds_unsafeSet {s : ContSet} {X : Set α} :
    (Specification.unsafeSet s).Holds X ↔ Disjoint X (construct s) := Iff.rfl

@[simp] theorem Specification.holds_invariant {s : ContSet} {X : Set α} :
    (Specification.invariant s).Holds X ↔ X ⊆ construct s := Iff.rfl

/-- CORA's `'custom'`: a predicate on the whole set, proved hereditary under
`⊆` (`mono`) and closed under the unions `holds_iUnion` needs
(`iUnionClosed`) — which makes it exactly a safe set, per `holds_custom_iff`. -/
def Specification.custom (p : Set α → Prop)
    (_mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (_iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i)) :
    Specification (Set α) :=
  Specification.safeSet (⋃ h : {S : Set α // p S}, h.1)

theorem Specification.holds_custom_iff (p : Set α → Prop)
    (mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i))
    {X : Set α} : (Specification.custom p mono iUnionClosed).Holds X ↔ p X := by
  rw [Specification.custom, Specification.holds_safeSet, ContSet.construct_set]
  refine ⟨fun hsub => mono hsub (iUnionClosed fun h => h.2), fun hpX => ?_⟩
  exact Set.subset_iUnion (fun h : {S : Set α // p S} => h.1) ⟨X, hpX⟩

/-- A requirement is normally several of these at once, all stored alike. -/
def Specification.HoldsAll (specs : List (Specification ContSet)) (X : Set α) : Prop :=
  ∀ spec ∈ specs, spec.Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
