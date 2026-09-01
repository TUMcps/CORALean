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

`Mtimes` alone keeps a family indexed by ℕ, because it is the one operation that
moves between ambient types and the result has to land somewhere. Size is not in
the index: a representation grows as it is operated on, and `reduce` is what
brings it back, where the algorithm asks for it rather than after every
operation.
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

/-- `x ∈ s` for a representation means what it denotes. Membership is what
nearly every guarantee states, so it is worth the notation; `construct` stays
available for the times a proof has to name the set itself. -/
instance {S α : Type} [ContSet S α] : Membership α S := ⟨fun s x => x ∈ construct s⟩

theorem ContSet.mem_iff {S α : Type} [ContSet S α] {s : S} {x : α} :
    x ∈ s ↔ x ∈ construct s := Iff.rfl

open Scalar

/-- A matrix denotes itself, read into ℝ by the layer's scalar. What makes a
statement about a set of matrices cover the plain one for free. -/
instance {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} : ContSet (Mat 𝕋 m n) (Mat ℝ m n) where
  construct M := {toRealMat M}

@[simp] theorem ContSet.construct_mat {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    construct M = {toRealMat M} := rfl

/-- What `M` stands for as a map: the set of linear maps `α → β` it denotes. A
plain matrix denotes one, an interval matrix denotes all the matrices between
its bounds.

`α` is an input and only `β` an `outParam`, which is what lets one matrix type
act on several ambient types: `Mat ℝ p q` sends `Vec ℝ q` to `Vec ℝ p` and
`Mat ℝ q r` to `Mat ℝ p r`, and the two instances are told apart by the ambient
type they are applied at. That matching is MATLAB's `pagemtimes` condition. -/
class LinMapSet (M : Type) (α : Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β] where
  denote : M → Set (α →ₗ[ℝ] β)

/-- Left multiplication by a matrix, on matrices. -/
def matMulLeft {p q r : ℕ} (M : Mat ℝ p q) : Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun B := M * B
  map_add' := Matrix.mul_add M
  map_smul' c B := Matrix.mul_smul M c B

/-- Right multiplication by a matrix, on matrices. The other side of
`pagemtimes`, and a different instance because it matches a different ambient
type. -/
def matMulRight {p q r : ℕ} (M : Mat ℝ q r) : Mat ℝ p q →ₗ[ℝ] Mat ℝ p r where
  toFun B := B * M
  map_add' B C := Matrix.add_mul B C M
  map_smul' c B := Matrix.smul_mul c B M

/-- A matrix acting on vectors. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} : LinMapSet (Mat 𝕋 p q) (Vec ℝ q) (Vec ℝ p) where
  denote M := {Matrix.mulVecLin (toRealMat M)}

/-- The same matrix acting on matrices, from the left. Distinguished from the
vector instance by the ambient type it is applied at. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMapSet (Mat 𝕋 p q) (Mat ℝ q r) (Mat ℝ p r) where
  denote M := {matMulLeft (toRealMat M)}

/-- Multiplication by anything denoting matrices, covering the interval matrix a
discretization produces as well as the plain one.

The guarantee is over everything the argument denotes, which at a plain matrix
is the one map it is, so this says exactly what a single map did. -/
class Mtimes (𝕄 : ℕ → ℕ → Type) (S : ℕ → Type)
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] where
  mtimes {m n : ℕ} : 𝕄 m n → S n → S m
  mtimes_outer {m n : ℕ} (M : 𝕄 m n) (s : S n) :
    (⋃ A ∈ construct M, (A *ᵥ ·) '' construct s) ⊆ construct (mtimes M s)

/-- Every point on a segment running from one set to the other. Named because
`linComb`, each instance and the float refinement all state it. -/
def segments {α : Type} [AddCommGroup α] [Module ℝ α] (X Y : Set α) : Set α :=
  {x | ∃ y₁ ∈ X, ∃ y₂ ∈ Y, ∃ lam ∈ Set.Icc (0:ℝ) 1, x = lam • y₁ + (1 - lam) • y₂}

/-- Outer only, so an algorithm proved against this says nothing about how much
precision a representation loses.

Every operation here takes and returns the same ambient type, so the class is
over a single representation rather than a family indexed by dimension.
`mtimes` is the one operation that moves between ambient types, and it is
`Mtimes` for that reason: an algorithm that travels between dimensions asks for
both, and one that does not asks for this alone.

The scalar the representation computes in appears in none of these, so it is not
a parameter either. -/
class OuterContSet (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  plus : S → S → S
  /-- CORA's `linComb`. Not the convex hull — the two agree only when both sets
  are convex, and this is the one a time-interval enclosure needs, since it is
  what keeps a non-convex representation non-convex. -/
  linComb : S → S → S
  /-- To a maximum order, read in the representation's own terms. Sound for any
  target, so the order is a precision knob and never a correctness one. -/
  reduce : S → ℕ → S
  plus_outer (s₁ s₂ : S) :
    construct s₁ + construct s₂ ⊆ construct (plus s₁ s₂)
  linComb_outer (s₁ s₂ : S) :
    segments (construct s₁) (construct s₂) ⊆ construct (linComb s₁ s₂)
  reduce_outer (s : S) (o : ℕ) :
    construct s ⊆ construct (reduce s o)

/-- Althoff's and CORA's symbol for the Minkowski sum, and deliberately not `+`:
`plus` is only *outer*, so `construct (s₁ ⊞ s₂)` merely contains
`construct s₁ + construct s₂`, and with `Pointwise` open both would otherwise
appear as `+` in one goal with only their arguments telling them apart. -/
scoped infixl:65 " ⊞ " => OuterContSet.plus

-- No `class abbrev` bundling these binders. It reads well, but every use adds an
-- unfolding step to instance search, and at the 5000-heartbeat budget that turns
-- `LinearSysDT.reach` and `Interval.abs_sub_center_le` into timeouts rather than
-- into slow proofs. The budget exists to make searching fail loudly; the
-- convenience is what gives way.


/-- Multiplication by anything denoting linear maps, at any pair of ambient
types. `Mtimes` is this at vectors, kept separate because there the dimension
moves and the family index is what says where the result lands.

`T`, `α` and `β` are all read off `M` and `S`, so a use site names none of
them. -/
class LinMtimes (M S : Type) (T : outParam Type) (α : outParam Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [ContSet S α] [ContSet T β] [LinMapSet M α β] where
  lmtimes : M → S → T
  lmtimes_outer (m : M) (s : S) :
    (⋃ f ∈ LinMapSet.denote (β := β) m, f '' construct s) ⊆ construct (lmtimes m s)

end CORALean
