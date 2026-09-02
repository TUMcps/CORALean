import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.NN.Layer

/-!
# The linear layer over a floating-point scalar

`x ↦ W x + b` with `W` and `b` stored as floats, and the function it encloses is
the exact affine map those stored floats denote — not the one an implementation
computes, and not one the weights are only close to. Reading a network off a
file is exact; everything after it rounds.

Nothing rounds here either, and that is worth stating rather than apologising
for. The definition is the exact layer's, term for term: the weights multiply
through `mtimes` and the bias enters as a box of zero width through `plus`, and
both of those already pay their own rounding into the representation's error
box. A layer that added a rounding of its own would be paying twice.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix Pointwise ContSet Plus Mtimes OfInterval SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋] {n m : ℕ}

def Layer.linear (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : Real.Layer S n m where
  eval x := toRealMat W *ᵥ x + toRealVec b
  propagate s := plus (mtimes W s) (ofInterval (Interval.point b))
  propagate_outer s _x hx :=
    plus_outer _ _ (Set.add_mem_add
      (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ (Interval.mem_point b)))

end CORALean.Float
