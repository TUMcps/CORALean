module

public import CORALean.NN.Operations.LayerSensitivity
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# Reading a layer's sensitivity off a matrix

A layer whose derivative at `x` is a matrix has that matrix as its sensitivity.
The bridge every instantiation crosses, so that a layer supplies a `HasFDerivAt`
and knows nothing about `toMatrix'`.

The derivative is asked for as the continuous linear map a matrix induces rather
than as an abstract one, which is what makes `toMatrix'` invert it on the nose.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.sensitivity_eq_of_hasFDerivAt {f : Vec ℝ n → Vec ℝ m} {A : Mat ℝ m n}
    {x : Vec ℝ n}
    (h : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) x) :
    layerSensitivity f x = A := by
  rw [layerSensitivity, h.fderiv, LinearMap.coe_toContinuousLinearMap,
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
