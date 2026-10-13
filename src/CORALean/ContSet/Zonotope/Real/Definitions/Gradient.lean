module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# The gradient of a function with respect to a zonotope

[1, Def. 3]: `∇_Z f(Z) = ⟨∇_c f(Z), ∇_G f(Z)⟩_Z`, the zonotope whose centre is the derivative of
`f` with respect to the centre and whose generator matrix is its derivative with respect to the
generator matrix, `(∇_c f)(i) = ∂f/∂c(i)` and `(∇_G f)(i,j) = ∂f/∂G(i,j)`. Each entry is the
derivative of `f` along that one entry, the others held fixed, so the generator count stays that
of `Z`. `deriv` is zero where `f` is not differentiable along an entry, so what the gradient is
at such a point is not claimed.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope of `f`'s partial derivatives along the centre and generator entries of `Z`. -/
noncomputable def Zonotope.gradient (f : Zonotope (Vec ℝ n) → ℝ) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) where
  h := Z.h
  c := fun i => deriv (fun t => f { Z with c := Function.update Z.c i t }) (Z.c i)
  G := fun j i => deriv
    (fun t => f { Z with G := Function.update Z.G j (Function.update (Z.G j) i t) }) (Z.G j i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
