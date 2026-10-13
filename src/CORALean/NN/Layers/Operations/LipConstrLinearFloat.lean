import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.NN.Layers.Operations.LipConstrScaleFloat
import CORALean.NN.Layers.Layer

/-!
# The Lipschitz-constrained linear layer, over a float scalar

`Layer.lipConstrLinear` run on stored weights. `N` is only known to lie in the box
`Layer.lipConstrScaleFloat`, so `N W` and `N b` are interval matrices and vectors: each entry is
the corner hull of the scaling's box against the stored weight, rounded outward. The weights
act through `mtimes` at an interval matrix and the bias enters as a box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes Float.OfInterval

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (fun m n => Float.Interval (Mat 𝕋 m n)) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `N (W x + b)` with `N W` and `N b` enclosed entrywise, then `mtimes` and `plus`. -/
def Layer.lipConstrLinearFloat (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (lam : 𝕋) : Layer S n m where
  enclose s :=
    let N : Float.Interval (Vec 𝕋 m) := Layer.lipConstrScaleFloat W lam
    plus (mtimes (𝕄 := fun m n => Float.Interval (Mat 𝕋 m n))
      ⟨fun i j => Float.Interval.mulLo (N.inf i) (N.sup i) (W i j) (W i j),
       fun i j => Float.Interval.mulHi (N.inf i) (N.sup i) (W i j) (W i j)⟩ s)
      (ofInterval ⟨fun i => Float.Interval.mulLo (N.inf i) (N.sup i) (b i) (b i),
                   fun i => Float.Interval.mulHi (N.inf i) (N.sup i) (b i) (b i)⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
