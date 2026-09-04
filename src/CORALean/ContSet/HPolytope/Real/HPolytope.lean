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
-- Last update:   04-September-2026
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

end CORALean.Real
