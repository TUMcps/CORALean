import CORALean.Global.API

/-!
# Set representations

CORA's `contSet`: one field, `construct`, sending a representation to the set it
denotes.

It belongs to neither layer: the set is always over ℝ, whichever arithmetic the
representation is written in, and both layers instantiate the same class. So
over-approximation and refinement are the single relation
`X ⊆ ContSet.construct S`, and the two compose by transitivity.

`OuterContSet` adds the operations an algorithm needs, each with the guarantee
that makes it usable. A mixin, not an extension, so a representation keeps the
one `ContSet` instance it already has.

`construct` is meaningful at strictly more types than the operations are — a
zonotope denotes a set at every generator count, but is closed at only one — so
the two cannot become one class.

`𝕋` is the scalar the representation computes in: ℝ in a `Real` directory, a
machine scalar in a `Float` one. `Global.Scalar` says how to read a matrix of
them, and is its own class so a statement about the matrix alone — a trajectory,
say — need not name a set representation.

The class is indexed by the ambient type rather than by a dimension, so a
representation of a set of *matrices* is an instance like any other and a plain
matrix denotes the singleton it is. Not by a `Tensor` shape: `Mat` is Mathlib's
`Matrix`, equal to `Tensor ℝ [m, n]` only up to `rfl`, and instance search sees
through that in neither direction.

The operation classes still take a family indexed by ℕ, because `mtimes` moves
the dimension and the result has to land somewhere. Size is not in the index: a
representation grows as it is operated on, and `reduce` is what brings it back,
where the algorithm asks for it rather than after every operation.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean

open Matrix Pointwise

class ContSet (S : Type) (α : outParam Type) where
  construct : S → Set α

open ContSet

open Scalar

/-- A matrix denotes itself, read into ℝ by the layer's scalar. What makes a
statement about a set of matrices cover the plain one for free. -/
instance {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} : ContSet (Mat 𝕋 m n) (Mat ℝ m n) where
  construct M := {toRealMat M}

@[simp] theorem ContSet.construct_mat {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    construct M = {toRealMat M} := rfl

/-- Multiplication by anything denoting matrices, covering the interval matrix a
discretization produces as well as the plain one.

The guarantee is over everything the argument denotes, which at a plain matrix
is the one matrix it is, so this says exactly what a single map did. -/
class Mtimes (𝕄 : ℕ → ℕ → Type) (S : ℕ → Type)
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] where
  mtimes {m n : ℕ} : 𝕄 m n → S n → S m
  mtimes_outer {m n : ℕ} (M : 𝕄 m n) (s : S n) :
    (⋃ A ∈ construct M, (A *ᵥ ·) '' construct s) ⊆ construct (mtimes M s)

/-- Every point on a segment running from one set to the other. Named because
`linComb`, each instance and the float refinement all state it. -/
def segments {n : ℕ} (X Y : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ y₁ ∈ X, ∃ y₂ ∈ Y, ∃ lam ∈ Set.Icc (0:ℝ) 1, x = lam • y₁ + (1 - lam) • y₂}

/-- Outer only, so an algorithm proved against this says nothing about how much
precision a representation loses.

`𝕋` is an `outParam`: it is fixed by the representation and appears in none of
`plus`, `linComb` or `reduce`, so instance search must read it off `S`, not the
use site.

`mtimes` is inherited rather than declared, so a representation may also carry
it at other matrix types without this class knowing. -/
class OuterContSet (S : ℕ → Type) (𝕋 : outParam Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [Scalar 𝕋] extends Mtimes (Mat 𝕋) S where
  plus {n : ℕ} : S n → S n → S n
  /-- CORA's `linComb`. Not the convex hull — the two agree only when both sets
  are convex, and this is the one a time-interval enclosure needs, since it is
  what keeps a non-convex representation non-convex. -/
  linComb {n : ℕ} : S n → S n → S n
  /-- To a maximum order, read in the representation's own terms. Sound for any
  target, so the order is a precision knob and never a correctness one. -/
  reduce {n : ℕ} : S n → ℕ → S n
  plus_outer {n : ℕ} (s₁ s₂ : S n) :
    construct s₁ + construct s₂ ⊆ construct (plus s₁ s₂)
  linComb_outer {n : ℕ} (s₁ s₂ : S n) :
    segments (construct s₁) (construct s₂) ⊆ construct (linComb s₁ s₂)
  reduce_outer {n : ℕ} (s : S n) (o : ℕ) :
    construct s ⊆ construct (reduce s o)

end CORALean
