import CORALean.Global.Tensor

/-!
# What a computed set is checked against

CORA's `specification`: a set together with what it means. A safe set is one
every point must lie in, an unsafe set one no point may lie in — the two ways a
requirement is written, and the reason `Holds` is one match rather than two
definitions. CORA's other kinds are absent: `invariant` stops the analysis
rather than judging it, and `custom` and `logic` are not sets.

Stated over `Set α` and not over a representation, because the check is what an
outer approximation is *for*: `Theorems.HoldsOfOuter` carries it from the
computed set to the exact one, and that step knows nothing about how either set
was described. So the same specification checks a reachable set and a network's
output set.
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

structure Specification (α : Type) where
  set : Set α
  kind : Specification.Kind

/-- Membership required of every point, or of none. -/
def Specification.Holds (spec : Specification α) (X : Set α) : Prop :=
  match spec.kind with
  | .safeSet => X ⊆ spec.set
  | .unsafeSet => Disjoint X spec.set

def Specification.safeSet (S : Set α) : Specification α := ⟨S, .safeSet⟩

def Specification.unsafeSet (S : Set α) : Specification α := ⟨S, .unsafeSet⟩

@[simp] theorem Specification.holds_safeSet {S X : Set α} :
    (Specification.safeSet S).Holds X ↔ X ⊆ S := Iff.rfl

@[simp] theorem Specification.holds_unsafeSet {S X : Set α} :
    (Specification.unsafeSet S).Holds X ↔ Disjoint X S := Iff.rfl

/-- A requirement is normally several of these at once. -/
def Specification.HoldsAll (specs : List (Specification α)) (X : Set α) : Prop :=
  ∀ spec ∈ specs, spec.Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
