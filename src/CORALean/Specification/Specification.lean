import CORALean.Global.Tensor

/-!
# What a computed set is checked against

CORA's `specification`: a set together with what it means. A safe set is one
every point must lie in, an unsafe set one no point may lie in, and an
invariant is checked the same way as a safe set — `check.m`'s numeric branch
and `robustness.m` run the identical test for `'safeSet'` and `'invariant'`,
differing only in name and in use (a location's invariant, already
`HybridDynamics.Location.inv`, not a goal). Three kinds, two definitions, why
`Holds` is one match.

`custom` is not a fourth kind: CORA's version is an arbitrary user function
with no guarantee it survives an outer approximation, so `Specification.custom`
instead packages one that provably does, pinning it down to being a safe
set — see its own docstring. `logic`, signal temporal logic, is out of scope:
satisfying one is model checking over a different language. Stated over
`Set α`, not a representation, since the check is what an outer approximation
is *for*: `Theorems.HoldsOfOuter` carries it to the exact set, knowing
nothing of how either was described.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive Specification.Kind
  | safeSet
  | unsafeSet
  | invariant

structure Specification (α : Type) where
  set : Set α
  kind : Specification.Kind

/-- Membership required of every point, or of none. -/
def Specification.Holds (spec : Specification α) (X : Set α) : Prop :=
  match spec.kind with
  | .safeSet => X ⊆ spec.set
  | .unsafeSet => Disjoint X spec.set
  | .invariant => X ⊆ spec.set

def Specification.safeSet (S : Set α) : Specification α := ⟨S, .safeSet⟩

def Specification.unsafeSet (S : Set α) : Specification α := ⟨S, .unsafeSet⟩

/-- CORA's `'invariant'` type: checked as `contains(set, S)`, the same test as
`safeSet` — see `check.m`'s numeric branch and `robustness.m`. -/
def Specification.invariant (S : Set α) : Specification α := ⟨S, .invariant⟩

@[simp] theorem Specification.holds_safeSet {S X : Set α} :
    (Specification.safeSet S).Holds X ↔ X ⊆ S := Iff.rfl

@[simp] theorem Specification.holds_unsafeSet {S X : Set α} :
    (Specification.unsafeSet S).Holds X ↔ Disjoint X S := Iff.rfl

@[simp] theorem Specification.holds_invariant {S X : Set α} :
    (Specification.invariant S).Holds X ↔ X ⊆ S := Iff.rfl

/-- CORA's `'custom'`: a predicate on the whole set, proved hereditary under
`⊆` (`mono`) and closed under the unions `holds_iUnion` needs
(`iUnionClosed`) — which makes it exactly a safe set, per `holds_custom_iff`. -/
def Specification.custom (p : Set α → Prop)
    (_mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (_iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i)) :
    Specification α :=
  Specification.safeSet (⋃ h : {S : Set α // p S}, h.1)

theorem Specification.holds_custom_iff (p : Set α → Prop)
    (mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i))
    {X : Set α} : (Specification.custom p mono iUnionClosed).Holds X ↔ p X := by
  rw [Specification.custom, Specification.holds_safeSet]
  refine ⟨fun hsub => mono hsub (iUnionClosed fun h => h.2), fun hpX => ?_⟩
  exact Set.subset_iUnion (fun h : {S : Set α // p S} => h.1) ⟨X, hpX⟩

/-- A requirement is normally several of these at once. -/
def Specification.HoldsAll (specs : List (Specification α)) (X : Set α) : Prop :=
  ∀ spec ∈ specs, spec.Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
