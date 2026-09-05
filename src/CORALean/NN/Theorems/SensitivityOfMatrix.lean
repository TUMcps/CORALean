import CORALean.NN.Operations.LayerSensitivity

/-!
# Reading a layer's sensitivity off a matrix

A layer whose derivative at `x` is a matrix has that matrix as its sensitivity.
The bridge every instantiation crosses, so that a layer supplies a `HasFDerivAt`
and knows nothing about `toMatrix'`.

The derivative is asked for as the continuous linear map a matrix induces rather
than as an abstract one, which is what makes `toMatrix'` invert it on the nose.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

theorem Layer.sensitivity_eq_of_hasFDerivAt {L : Layer S n m} {A : Mat ℝ m n} {x : Vec ℝ n}
    (h : HasFDerivAt L.eval (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) x) :
    L.sensitivity x = A := by
  rw [Layer.sensitivity, h.fderiv, LinearMap.coe_toContinuousLinearMap,
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

end CORALean.Real
