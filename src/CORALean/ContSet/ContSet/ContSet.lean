import CORALean.Global.Scalar

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
rather than all of it, and an algorithm names what it calls. There is
deliberately no class collecting them: a bundle would make every representation
owe every operation, and the one that cannot compute one would have to invent it.

Indexed by the ambient type rather than by a dimension, so a representation of a
set of *matrices* is an instance like any other. Not by a `Tensor` shape: `Mat`
is Mathlib's `Matrix`, equal to `Tensor ℝ [m, n]` only up to `rfl`, and instance
search sees through that in neither direction.

`Mtimes` and `Reindex` keep a family indexed by ℕ, being the operations that
move between ambient types, where the result has to land somewhere.

`Reindex` is the only class here whose field is an *equality*. That is what it
is for: relabelling coordinates loses nothing, and a permutation matrix pushed
through `mtimes` would compute the same set without any way to say so.

## A precision parameter, and where it goes

Several operations take one. `Ellipsoid.plus` takes the scaling that decides how
tight the enclosure of the sum is — two of them at the float layer, that being
the honest parameter and `l` the number they are derived from —
`HPolytope.plusOf` the directions the result is described on together with a
bound in each, `VPolytope.and` two families of directions, and `Reduce` carries
its knob, the order `o`, in the signature. None of the operation classes takes
one, and the reason divides in two: whether the parameter depends on the
operands.

*Operand-independent.* `Ellipsoid.plus_outer` holds at one fixed `l > 0` for
every pair of ellipsoids, so the parameter can simply be closed over.
`Ellipsoid.plusInstance` is a `def` returning `Plus`, never an `instance`:
search does not find it, so the caller writes `letI := Ellipsoid.plusInstance hl`
and the choice is theirs and visible. The class is unchanged, the twelve `Plus`
instances already here are untouched, no use site moves, and every algorithm
written against `Plus` runs at an ellipsoid the moment the scaling is named.
It is `SupportBound`'s own discipline one level up — a value together with the
proof that makes it legal, supplied by whoever holds it. `Reduce`'s `o` is the
degenerate case of the same thing, absorbed into the signature because a natural
number is a parameter every representation already has.

*Operand-dependent.* `HPolytope.plusOf` wants a `SupportBound P.construct (Aq i)`
for each operand, and no class field reaches that. `plus : S → S → S` is total,
so an instance needs bounds for *every* polytope, not for the two a caller holds
— a recursive algorithm sums sets produced inside the recursion, step `k+1` of
`LinearSysDT.reach` naming a set the caller never sees. That is an oracle, and
here not even a missing one: a halfspace description with no rows denotes the
whole space, which has no support bound in any non-zero direction, so outside
the degenerate zero direction the oracle is uninhabited. A *useful* `Plus` at
`HPolytope` needs a type excluding unbounded sets before it needs a linear
program. So the obstacle there is neither the class shape nor a class field.

That leaves nothing for a parameter in the class to buy, and three ways of
putting one there that each cost something.

*A `Param` field* — `Param : Type := Unit` and `plus : Param → S → S → S` —
fails twice. `HPolytope`'s parameter names its operand, so the field would have
to read `Param : S → S → Type` and `plus` become dependently typed, which `⊞`
and every rewrite through `plus` would carry from there on. And the value has to
come from somewhere: a generic algorithm cannot produce one, so `Param` becomes
an argument of the algorithm and then of every theorem naming it — `Plus` is a
binder in forty-seven files and is called in sixteen.

*An `outParam Param`* fixes only the first half of that. Search would infer
`Unit` wherever no knob is needed, so no representation invents one; but an
`outParam` names the type and never the value, so every call site still grows an
argument and every algorithm still has to be handed one.

*A second class `PlusParam`, with `Plus` derived by fixing a default*, leaves
those sites alone and buys nothing: the derivation is exactly the buried
precision choice, so the representation that has a knob never uses it.

The price of the choice is that one instance fixes the parameter for a whole
run, where the tightest scalings depend on the two operands and on the
direction. That is precision and never soundness, and a caller wanting it per
call names `Ellipsoid.plus` directly. What it does not buy is a reachability
loop at an ellipsoid: today only `LinearSys.inputTaylorSum` runs, the loops
still wanting `Reduce`, `LinComb`, `OfInterval` and `Mtimes ℐ`. Those are
missing operations rather than missing room for a parameter, and keeping the two
apart is what this section is for.

`And` is answered in advance. `Interval.and`, `HPolytope.and`, `ConZonotope.and`
and `ConPolyZono.and` are all `S → S → S` and would be plain instances;
`VPolytope.and` takes two families of directions, because it goes out through
halfspaces and comes back, and its parameter is operand-independent, so it would
get an `andInstance`. The class stays unwritten because nothing yet intersects
generically — a missing consumer, not a missing knob.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   03-September-2026
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

/-- Relabelling coordinates, bundled: a reindexing is a linear map, which is
what lets a representation closed under `map` discharge the guarantee below with
the exactness proof it already has. -/
def reindexLin {n m : ℕ} (e : Fin m ≃ Fin n) : Vec ℝ n →ₗ[ℝ] Vec ℝ m where
  toFun x := fun i => x (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reading a set's coordinates in a different order, and the one operation
class here whose guarantee is an *equality*. That is why it is not `Mtimes` at a
permutation matrix: the matrix product computes the same set, but `mtimes_outer`
has no room to say so, and a reshape layer's whole content is that it loses
nothing.

`Fin m ≃ Fin n` rather than a plain `Fin m → Fin n`: a zonotope is exact under
any reindexing, but a box is not — duplicating a coordinate constrains the two
copies to agree, and an axis-aligned box cannot say that. -/
class Reindex (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  reindex {n m : ℕ} : (Fin m ≃ Fin n) → S n → S m
  reindex_exact {n m : ℕ} (e : Fin m ≃ Fin n) (s : S n) :
    construct (reindex e s) = reindexLin e '' construct s

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

-- No class bundling these three. An algorithm names the operations it calls, a
-- representation instantiates the ones it computes, and neither has to pretend:
-- a representation with no `linComb` still runs everything that never combines.

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
