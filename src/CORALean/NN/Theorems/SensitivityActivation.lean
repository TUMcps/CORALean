import CORALean.NN.Layers.Activation
import CORALean.NN.Theorems.SensitivityOfMatrix

/-!
# An activation layer's sensitivity is diagonal

One neuron per coordinate, so the Jacobian couples nothing: `σ'` evaluated at
each coordinate of the point, down the diagonal. CORA's
`nnActivationLayer/evaluateSensitivity` writes the same thing as a scaling of
the incoming rows by `df` at the stored input.

The relaxation takes no part — `eval` is `σ` coordinatewise whichever one the
layer carries — so the hypothesis is on `σ` alone, and every layer built on a
differentiable activation gets this at its own derivative.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.IntervalOuter Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activation_sensitivity {σ σ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt σ (σ' t) t)
    (x : Vec ℝ n) :
    layerSensitivity (fun (y : Vec ℝ n) i => σ (y i)) x
      = Matrix.diagonal fun i => σ' (x i) := by -- --- PROOF ---
  refine Layer.sensitivity_eq_of_hasFDerivAt ?_
  rw [hasFDerivAt_pi']
  intro i
  -- coordinate `i` is `σ` after a projection, so the scalar chain rule gives it
  have hproj : HasFDerivAt (fun y : Vec ℝ n => y i) (ContinuousLinearMap.proj i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
  refine ((hd (x i)).comp_hasFDerivAt x hproj).congr_fderiv ?_
  ext v
  show σ' (x i) * v i = (Matrix.diagonal (fun i => σ' (x i)) *ᵥ v) i
  rw [Matrix.mulVec_diagonal]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
