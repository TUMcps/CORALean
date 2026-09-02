import CORALean.ContSet.ContSet.ContSet

/-!
# Polytopes: the halfspace representation

CORA's `polytope` with `isHRep` set: the points satisfying finitely many
inequalities `A x ≤ b` and equalities `Ae x = be`.

A constraint is a linear functional rather than a matrix row, so the
representation lives at any real module; `ofMat` reads CORA's matrices into it.

Exact under intersection and preimage, and under nothing else — a Minkowski sum
or a convex hull of two halfspace descriptions needs vertex enumeration. That is
what `VPolytope` is for, the two representations being good at disjoint
operations.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure HPolytope (α : Type) [AddCommGroup α] [Module ℝ α] where
  m : ℕ
  A : Fin m → (α →ₗ[ℝ] ℝ)
  b : Fin m → ℝ
  me : ℕ
  Ae : Fin me → (α →ₗ[ℝ] ℝ)
  be : Fin me → ℝ

def HPolytope.construct (P : HPolytope α) : Set α :=
  {x | (∀ i, P.A i x ≤ P.b i) ∧ ∀ i, P.Ae i x = P.be i}

theorem HPolytope.mem_construct_iff {P : HPolytope α} {x : α} :
    x ∈ P.construct ↔ (∀ i, P.A i x ≤ P.b i) ∧ ∀ i, P.Ae i x = P.be i := Iff.rfl

/-- No constraints, so every point qualifies: the unit of `and`. -/
def HPolytope.fullspace (α : Type) [AddCommGroup α] [Module ℝ α] : HPolytope α where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.construct_fullspace : (HPolytope.fullspace α).construct = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- One unsatisfiable row, `0 ≤ -1`: the absorbing element of `and`, and what a
halfspace description says when it has nothing. -/
def HPolytope.emptySet (α : Type) [AddCommGroup α] [Module ℝ α] : HPolytope α where
  m := 1
  A := fun _ => 0
  b := fun _ => -1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.construct_emptySet : (HPolytope.emptySet α).construct = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hle, -⟩
  -- the row index ascribed at `Fin 1`, the count's reduced spelling
  have h : (0:ℝ) ≤ -1 := hle (0 : Fin 1)
  linarith

end CORALean.Real
