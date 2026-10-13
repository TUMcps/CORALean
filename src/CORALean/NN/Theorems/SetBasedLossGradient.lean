import CORALean.NN.Definitions.SetBasedLoss
import CORALean.ContSet.Zonotope.Real.Theorems.FRadiusGradient

/-!
# The gradient of the set-based loss

[1, Prop. 9]: the gradient of the set-based loss `𝓛(t, Y)` [1, Def. 5] at `Y = ⟨c_κ, G_κ⟩` is the
zonotope with centre `(1 - τ) ∇_c L(t, c_κ)` and generator matrix `(τ/ε) G_κ / (n_κ² ‖Y‖_F)`, for
`Y ≠ ⟨c, 0⟩` and a loss differentiable along every entry of the centre. The paper prints the
generator matrix `(τ/ε) (1 / (n_κ ‖Y‖_F)) G_κ` Eq. 9 of [1, Prop. 9], inheriting the factor `n` of
[1, Prop. 8]; the centre is as printed, and the generator entries get the corrected
`Zonotope.fRadius_gradient`. The counterexample to the printed form is
`setBasedLoss_gradient_counterexample`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem setBasedLoss_gradient (L : Vec ℝ n → Vec ℝ n → ℝ) (τ ε : ℝ) (t : Vec ℝ n)
    (Y : Zonotope (Vec ℝ n)) (hY : 0 < Y.fRadius)
    (hL : ∀ i, DifferentiableAt ℝ (fun s => L t (Function.update Y.c i s)) (Y.c i)) :
    Y.gradient (setBasedLoss L τ ε t) =
      { h := Y.h
        c := fun i => (1 - τ) * deriv (fun s => L t (Function.update Y.c i s)) (Y.c i)
        G := fun j i => τ / ε * (Y.G j i / ((n : ℝ) ^ 2 * Y.fRadius)) } := by -- --- PROOF ---
  unfold Zonotope.gradient
  congr 1
  · funext i
    have h1 : (fun s => setBasedLoss L τ ε t { Y with c := Function.update Y.c i s }) =
        fun s => (1 - τ) * L t (Function.update Y.c i s) + τ / ε * Y.fRadius := rfl
    show deriv (fun s => setBasedLoss L τ ε t { Y with c := Function.update Y.c i s }) (Y.c i) = _
    rw [h1, deriv_add_const, deriv_const_mul _ (hL i)]
  · funext j i
    have h1 : (fun s => setBasedLoss L τ ε t
        { Y with G := Function.update Y.G j (Function.update (Y.G j) i s) }) =
        fun s => (1 - τ) * L t Y.c + τ / ε * Zonotope.fRadius
          { Y with G := Function.update Y.G j (Function.update (Y.G j) i s) } := rfl
    show deriv (fun s => setBasedLoss L τ ε t
      { Y with G := Function.update Y.G j (Function.update (Y.G j) i s) }) (Y.G j i) = _
    rw [h1]
    exact ((Zonotope.fRadius_hasDerivAt Y hY j i).const_mul (τ / ε) |>.const_add _).deriv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
