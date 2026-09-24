import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
import CORALean.NN.Layers.Operations.LinearWithError

/-!
# What the linear layer with an error box encloses

The affine map at `E`'s own centre: the layer commits to the centre of the box `E` denotes as
its nominal value, a real number with no reason to be rounded, and pays the rest of `E` into its
enclosure. That centre is inside `E` only when `E` is nonempty, which is the one hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.OfInterval Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The value committed to is the centre of the box `E` denotes, which is why `E` has to be
nonempty: an empty box has a centre no point of it. -/
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
