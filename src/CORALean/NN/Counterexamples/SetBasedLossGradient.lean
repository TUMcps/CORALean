module

public import CORALean.NN.Theorems.SetBasedLossGradient

@[expose] public section

/-!
# The gradient of the set-based loss as printed is off by a factor `n`

[1, Prop. 9] prints the generator matrix of `∇_Y 𝓛(t, Y)` as `(τ/ε) (1 / (n_κ ‖Y‖_F)) G_κ`. At
`n_κ = 2`, `τ = ε = 1`, the zero loss and the zonotope with the one generator `(1, 0)`, whose
F-radius is `1/2`, the printed entry at `G(0,0)` is `1 / (2 · 1/2) = 1`, while the derivative of
`𝓛 = ‖Y‖_F` along it is `1/2`: [1, Prop. 8]'s factor `n` again. The corrected form is
`setBasedLoss_gradient`.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem setBasedLoss_gradient_counterexample :
    ∃ Y : Zonotope (Vec ℝ 2), 0 < Y.fRadius ∧
      Y.gradient (setBasedLoss (fun _ _ => 0) 1 1 0) ≠
        { h := Y.h
          c := fun i => (1 - 1) * deriv (fun s => (fun (_ _ : Vec ℝ 2) => (0 : ℝ)) 0
            (Function.update Y.c i s)) (Y.c i)
          G := fun j i => 1 / 1 * (1 / (2 * Y.fRadius) * Y.G j i) } := by -- --- PROOF ---
  let Y : Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ i => if i = 0 then 1 else 0⟩
  have hF : Y.fRadius = 1 / 2 := by simp [Zonotope.fRadius, Y]
  have hpos : 0 < Y.fRadius := by rw [hF]; norm_num
  refine ⟨Y, hpos, fun h => ?_⟩
  rw [setBasedLoss_gradient _ _ _ _ Y hpos (fun i => differentiableAt_const _)] at h
  obtain ⟨-, -, hG⟩ := Zonotope.mk.inj h
  have h1 := congrFun (congrFun (eq_of_heq hG) (0 : Fin 1)) (0 : Fin 2)
  simp only [hF, Y] at h1
  norm_num at h1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
