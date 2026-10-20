module

public import CORALean.ContSet.Zonotope.Real.Theorems.FRadiusGradient

@[expose] public section

/-!
# The gradient of the F-radius as printed is off by a factor `n`

[1, Prop. 8] prints the gradient of `‖Y‖_F = (1/n) √(Σ G²)` [1, Prop. 5] as `⟨0, G / (n ‖Y‖_F)⟩`.
In two dimensions the zonotope with the one generator `(1, 0)` has `‖Y‖_F = 1/2` and the derivative
of `‖Y‖_F` along the entry `G(0,0) = 1` is `(1/2) · 1 / 1 = 1/2`, where the printed formula gives
`1 / (2 · 1/2) = 1`. The corrected gradient is `Zonotope.fRadius_gradient`, `G / (n² ‖Y‖_F)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the F-radius gradient differs from the claimed scaled copy

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.fRadius_gradient_counterexample : -- --- CONCL ---
    ∃ Y : Zonotope (Vec ℝ 2), 0 < Y.fRadius ∧
      Y.gradient Zonotope.fRadius ≠
        { h := Y.h, c := 0, G := fun j i => Y.G j i / (2 * Y.fRadius) } := by -- --- PROOF ---
  let Y : Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ i => if i = 0 then 1 else 0⟩
  have hF : Y.fRadius = 1 / 2 := by
    simp [Zonotope.fRadius, Y]
  have hpos : 0 < Y.fRadius := by rw [hF]; norm_num
  refine ⟨Y, hpos, fun h => ?_⟩
  rw [Zonotope.fRadius_gradient Y hpos] at h
  obtain ⟨-, -, hG⟩ := Zonotope.mk.inj h
  have h1 := congrFun (congrFun (eq_of_heq hG) (0 : Fin 1)) (0 : Fin 2)
  simp only [hF, Y] at h1
  norm_num at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
