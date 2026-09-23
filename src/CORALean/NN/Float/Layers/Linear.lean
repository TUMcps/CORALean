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
and the nominal value its soundness commits to is the centre of what that box
*denotes* — a real number, with no reason to be rounded at all.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise ContSet Plus Mtimes OfInterval SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋] {n m : ℕ}

def Layer.linear (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Interval.point b))

theorem Layer.linear_sound (W : Mat 𝕋 m n) (b : Vec 𝕋 m) :
    (Layer.linear (S := S) W b).Sound fun x => toRealMat W *ᵥ x + toRealVec b :=
  ⟨fun s _x hx => plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ (Interval.mem_point b)))⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` with an added error box, CORA's `W h + b ⊕ E`: the reduced
linear layer a neuron merge leaves behind, weights and box alike stored as
floats. -/
def Layer.linearWithError (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (E : Interval 𝕋 m) :
    Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) E))

/-- The value committed to is the centre of the box `E` denotes, which is why
`E` has to be nonempty. -/
theorem Layer.linearWithError_sound (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (E : Interval 𝕋 m)
    (hE : E.nominal.IsNonempty) :
    (Layer.linearWithError (S := S) W b E).Sound
      fun x => toRealMat W *ᵥ x + toRealVec b + E.nominal.center := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
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

/-- What the layer encloses at *every* value of the error, not only its centre:
`W x + c` for any `c` within what `E` denotes of `b`. -/
theorem Layer.linearWithError_mem (W : Mat 𝕋 m n) {b : Vec 𝕋 m} {c : Vec ℝ m}
    {E : Interval 𝕋 m} (hc : c - toRealVec b ∈ E.construct) (s : S n) {x : Vec ℝ n}
    (hx : x ∈ construct s) :
    toRealMat W *ᵥ x + c ∈
      construct ((Layer.linearWithError (S := S) W b E).enclose s) := by -- --- PROOF ---
  have hbox : toRealVec b + (c - toRealVec b) ∈ construct (Interval.plus (Interval.point b) E) :=
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b) hc)
  rw [add_sub_cancel] at hbox
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hbox))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
