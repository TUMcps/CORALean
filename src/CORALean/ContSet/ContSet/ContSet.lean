import CORALean.Global.API

/-!
# Set representations

CORA's `contSet`: one field, `construct`, sending a representation to the set it
denotes. The set is always over ℝ, whichever arithmetic the representation
computes in, so over-approximation and refinement are the one relation
`X ⊆ construct s` and compose by transitivity.

Then one class per operation — `Plus`, `LinComb`, `Reduce` — each carrying the
guarantee that makes the operation usable. Separate from `ContSet`, since
`construct` is meaningful at strictly more types than the operations are: a
zonotope denotes a set over any real module, but `reduce` needs coordinates, and
a plain matrix denotes the singleton it is without being closed under anything.
Separate from each other, so that a representation instantiates what it computes
rather than all of it, and an algorithm names what it calls. `OuterContSet`
collects the three that `LinearSys` reachability happens to call.

Indexed by the ambient type rather than by a dimension, so a representation of a
set of *matrices* is an instance like any other. Not by a `Tensor` shape: `Mat`
is Mathlib's `Matrix`, equal to `Tensor ℝ [m, n]` only up to `rfl`, and instance
search sees through that in neither direction.

`Mtimes` alone keeps a family indexed by ℕ, since it is the one operation that
moves between ambient types and the result has to land somewhere.
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

/-- `x ∈ s` for a representation means what it denotes. -/
instance {S α : Type} [ContSet S α] : Membership α S := ⟨fun s x => x ∈ construct s⟩

theorem ContSet.mem_iff {S α : Type} [ContSet S α] {s : S} {x : α} :
    x ∈ s ↔ x ∈ construct s := Iff.rfl

open Scalar

/-- A matrix denotes itself, read into ℝ by the layer's scalar. What makes a
statement about a set of matrices cover the plain one. -/
instance {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} : ContSet (Mat 𝕋 m n) (Mat ℝ m n) where
  construct M := {toRealMat M}

@[simp] theorem ContSet.construct_mat {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    construct M = {toRealMat M} := rfl

/-- The set of linear maps `α → β` that `M` denotes: a plain matrix denotes one,
an interval matrix all the matrices between its bounds.

`α` is an input and only `β` an `outParam`, which is what lets one matrix type
act on several ambient types — `Mat ℝ p q` sends `Vec ℝ q` to `Vec ℝ p` and
`Mat ℝ q r` to `Mat ℝ p r`, the instances told apart by the type applied at. -/
class LinMapSet (M : Type) (α : Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β] where
  denote : M → Set (α →ₗ[ℝ] β)

/-- Left multiplication by a matrix, on matrices. -/
def matMulLeft {p q r : ℕ} (M : Mat ℝ p q) : Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun B := M * B
  map_add' := Matrix.mul_add M
  map_smul' c B := Matrix.mul_smul M c B

/-- Right multiplication by a matrix, on matrices. -/
def matMulRight {p q r : ℕ} (M : Mat ℝ q r) : Mat ℝ p q →ₗ[ℝ] Mat ℝ p r where
  toFun B := B * M
  map_add' B C := Matrix.add_mul B C M
  map_smul' c B := Matrix.smul_mul c B M

/-- A matrix acting on vectors. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} : LinMapSet (Mat 𝕋 p q) (Vec ℝ q) (Vec ℝ p) where
  denote M := {Matrix.mulVecLin (toRealMat M)}

/-- The same matrix acting on matrices, from the left. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMapSet (Mat 𝕋 p q) (Mat ℝ q r) (Mat ℝ p r) where
  denote M := {matMulLeft (toRealMat M)}

/-- Multiplication by anything denoting matrices, covering the interval matrix a
discretization produces as well as the plain one. The guarantee is over
everything the argument denotes, which at a plain matrix is the one map it is. -/
class Mtimes (𝕄 : ℕ → ℕ → Type) (S : ℕ → Type)
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] where
  mtimes {m n : ℕ} : 𝕄 m n → S n → S m
  mtimes_outer {m n : ℕ} (M : 𝕄 m n) (s : S n) :
    (⋃ A ∈ construct M, (A *ᵥ ·) '' construct s) ⊆ construct (mtimes M s)

/-- Every point on a segment running from one set to the other. -/
def segments {α : Type} [AddCommGroup α] [Module ℝ α] (X Y : Set α) : Set α :=
  {x | ∃ y₁ ∈ X, ∃ y₂ ∈ Y, ∃ lam ∈ Set.Icc (0:ℝ) 1, x = lam • y₁ + (1 - lam) • y₂}

/-- One class per operation, as CORA gives each representation one method per
operation: a representation instantiates what it computes, an algorithm asks for
what it calls. Each is outer only, so a proof against one says nothing about how
much precision the representation loses.

These operations take and return the same ambient type, so each is a class over
a single representation rather than a family indexed by dimension. An algorithm
that also travels between dimensions asks for `Mtimes` on top. -/
class Plus (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  plus : S → S → S
  plus_outer (s₁ s₂ : S) :
    construct s₁ + construct s₂ ⊆ construct (plus s₁ s₂)

/-- CORA's `linComb`, not the convex hull: the two agree only when both sets are
convex, and this is what keeps a non-convex representation non-convex. -/
class LinComb (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  linComb : S → S → S
  linComb_outer (s₁ s₂ : S) :
    segments (construct s₁) (construct s₂) ⊆ construct (linComb s₁ s₂)

/-- To a maximum order, read in the representation's own terms. Sound for any
target, so the order is a precision knob and never a correctness one. -/
class Reduce (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  reduce : S → ℕ → S
  reduce_outer (s : S) (o : ℕ) :
    construct s ⊆ construct (reduce s o)

/-- The three operations `LinearSys` reachability calls, under the one name its
theorems ask for. A bundle and not a concept: a different algorithm wants a
different list, and a representation that computes only some of these still
instantiates those. -/
class OuterContSet (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] extends Plus S α, LinComb S α, Reduce S α

/-- Althoff's and CORA's symbol for the Minkowski sum, and deliberately not `+`:
`plus` is only *outer*, so `construct (s₁ ⊞ s₂)` merely contains
`construct s₁ + construct s₂`, and with `Pointwise` open the two would otherwise
appear alike in one goal. -/
scoped infixl:65 " ⊞ " => Plus.plus

-- No `class abbrev` bundling these binders: every use adds an unfolding step to
-- instance search, which at 5000 heartbeats produces timeouts rather than slow
-- proofs.

/-- Multiplication by anything denoting linear maps, at any pair of ambient
types. `Mtimes` is this at vectors, kept separate because there the dimension
moves and the family index is what says where the result lands. -/
class LinMtimes (M S : Type) (T : outParam Type) (α : outParam Type) (β : outParam Type)
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [ContSet S α] [ContSet T β] [LinMapSet M α β] where
  lmtimes : M → S → T
  lmtimes_outer (m : M) (s : S) :
    (⋃ f ∈ LinMapSet.denote (β := β) m, f '' construct s) ⊆ construct (lmtimes m s)

end CORALean
