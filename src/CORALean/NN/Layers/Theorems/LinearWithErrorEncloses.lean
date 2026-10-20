module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemCenter
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.LinearWithError

@[expose] public section

/-!
# What the linear layer with an error box encloses

The affine map at `E`'s own center: the layer commits to the center of the box `E` denotes as
its nominal value, a real number with no reason to be rounded, and pays the rest of `E` into its
enclosure. That center is inside `E` only when `E` is nonempty, which is the one hypothesis.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `E` – added error box

## Hypotheses
* `hE` – the error box is nonempty

## Conclusion
* the layer encloses the affine map shifted to the box's center
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.OfInterval Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The value committed to is the center of the box `E` denotes, which is why `E` has to be
nonempty: an empty box has a center no point of it. -/
theorem Layer.linearWithError_encloses (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (E : Interval (Vec 𝕋 m))
    (hE : E.nominal.IsNonempty) :
    (Layer.linearWithError (S := S) W b E).Encloses
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
