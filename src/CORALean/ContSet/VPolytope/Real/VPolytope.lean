import CORALean.ContSet.ContSet.ContSet

/-!
# Polytopes: the vertex representation

CORA's `polytope` with `isVRep` set: the convex hull of finitely many points,
written here as the convex combinations of them.

Over any real module, as a zonotope is, and for the same reason — nothing about
a convex combination mentions coordinates. Only the coefficient constraint
differs: `∑ βⱼ = 1` with `βⱼ ≥ 0` here, `|βⱼ| ≤ 1` there.

Zero vertices denote `∅`, no coefficient family over an empty index summing
to one.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure VPolytope (α : Type) where
  k : ℕ
  V : Fin k → α

def VPolytope.construct (P : VPolytope α) : Set α :=
  {x | ∃ β : Fin P.k → ℝ, (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 ∧ x = ∑ j, β j • P.V j}

end CORALean.Real
