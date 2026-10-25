module

public import CORALean.ContSet.Zonotope.Real.Definitions.FRadius
public import CORALean.ContSet.Zonotope.Real.Theorems.FRadiusHasDerivAt
public import CORALean.ContSet.Zonotope.Real.Definitions.Gradient
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The gradient of the F-radius

[1, Prop. 8]: the gradient of the F-radius of `Y = ⟨c, G⟩ ⊂ ℝⁿ` is a zonotope with center `0` and
generator matrix `G / (n² ‖Y‖_F)`, for `Y ≠ ⟨c, 0⟩`. The paper prints `G / (n ‖Y‖_F)` Eq. 13;
that is the gradient of `(1/n) √(Σ G²)` only with `‖Y‖_F` read as the unnormalized Frobenius norm
`n ‖Y‖_F`, while [1, Prop. 5] defines `‖Y‖_F` with the factor `1/n`:
`∂/∂G(i,j) (1/n) √S = G(i,j) / (n² ‖Y‖_F)`. CORA's `train.m` divides by the unnormalized norm and
scales by `1/n` outside, which is this. The counterexample to the printed form is
`Zonotope.fRadius_gradient_counterexample`. At the zero norm the F-radius is not differentiable
along any entry: `0 < ‖Y‖_F` is the hypothesis.

## Inputs
* `Y` – zonotope

## Hypotheses
* `hY` – F-radius positive

## Conclusion
* the gradient is the scaled generators with zero center

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.fRadius_gradient (Y : Zonotope (Vec ℝ n)) (hY : 0 < Y.fRadius) : -- --- CONCL ---
    Y.gradient Zonotope.fRadius =
      { h := Y.h, c := 0,
        G := fun j i => Y.G j i / ((n : ℝ) ^ 2 * Y.fRadius) } := by -- --- PROOF ---
  unfold Zonotope.gradient
  congr 1
  · funext i
    change deriv (fun _ => Zonotope.fRadius Y) (Y.c i) = 0
    exact deriv_const _ _
  · funext j i
    exact (Zonotope.fRadius_hasDerivAt Y hY j i).deriv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
