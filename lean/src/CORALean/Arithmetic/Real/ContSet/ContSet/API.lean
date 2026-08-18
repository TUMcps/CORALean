import CORALean.Global.API

/-!
# Set representations

CORA's `contSet`: one field, `construct`, sending a representation to the set it
denotes.

It lives in the real layer because that set is always over ℝ, whichever
arithmetic the representation is written in. `Arithmetic.Float` instantiates it
too, so over-approximation and refinement are the single relation
`X ⊆ ContSet.construct S`, and the two layers compose by transitivity.

`OuterContSet` adds the operations an algorithm needs, each with the guarantee
that makes it usable. A mixin, not an extension, so a representation keeps the
one `ContSet` instance it already has.

`construct` is meaningful at strictly more types than the operations are — a
zonotope denotes a set at every generator count, but is closed at only one — so
the two cannot become one class.

`𝕋` is the scalar the representation computes in: ℝ here, a machine scalar in
`Arithmetic.Float`. `Global.Scalar` says how to read a matrix of them, and is its
own class so a statement about the matrix alone — a trajectory, say — need not
name a set representation.

The carrier is a family, one member per dimension, because `mtimes` moves the
dimension and the result has to land somewhere. Size is not in the index: a
representation grows as it is operated on, and `reduce` is what brings it back,
where the algorithm asks for it rather than after every operation.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix Pointwise

class ContSet (S : Type) (n : outParam ℕ) where
  construct : S → Set (Vec ℝ n)

open ContSet

open Scalar

/-- Outer only, so an algorithm proved against this says nothing about how much
precision a representation loses.

`𝕋` is an `outParam`: it is fixed by the representation and does not appear in
`plus` or `reduce`, so instance search must read it off `S`, not the use site. -/
class OuterContSet (S : ℕ → Type) (𝕋 : outParam Type) [∀ n, ContSet (S n) n]
    [Scalar 𝕋] where
  plus {n : ℕ} : S n → S n → S n
  mtimes {m n : ℕ} : Mat 𝕋 m n → S n → S m
  /-- To a maximum order, read in the representation's own terms. Sound for any
  target, so the order is a precision knob and never a correctness one. -/
  reduce {n : ℕ} : ℕ → S n → S n
  plus_outer {n : ℕ} (s₁ s₂ : S n) :
    construct s₁ + construct s₂ ⊆ construct (plus s₁ s₂)
  mtimes_outer {m n : ℕ} (M : Mat 𝕋 m n) (s : S n) :
    (toRealMat M *ᵥ ·) '' construct s ⊆ construct (mtimes M s)
  reduce_outer {n : ℕ} (o : ℕ) (s : S n) :
    construct s ⊆ construct (reduce o s)

end CORALean.Arithmetic.Real
