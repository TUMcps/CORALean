import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
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

`Layer.linearWithError` is the same layer carrying the approximation error a
neuron merge leaves behind. It rounds nothing either: the box arrives in `𝕋`,
and the nominal value it commits to is the centre of what that box *denotes*,
since `eval` is a real function and has no reason to be rounded at all.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` with an added error box, CORA's `W h + b ⊕ E`: the reduced
linear layer a neuron merge leaves behind, weights and box alike stored as
floats. -/
noncomputable def Layer.linearWithError (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (E : Interval 𝕋 m)
    (hE : E.nominal.IsNonempty) : Real.Layer S n m where
  eval x := toRealMat W *ᵥ x + toRealVec b + E.nominal.center
  propagate s := plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E))
  propagate_outer s x hx := by
    -- the committed value is the centre of the box `E` denotes, which is inside it
    have hbox : toRealVec b + E.nominal.center
        ∈ construct (Interval.plus (Interval.point b) E) :=
      Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b)
        (Real.Interval.mem_center E.nominal hE))
    show toRealMat W *ᵥ x + toRealVec b + E.nominal.center ∈ construct
        (plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E)))
    rw [add_assoc]
    exact plus_outer _ _ (Set.add_mem_add
      (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      (ofInterval_outer _ hbox))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
