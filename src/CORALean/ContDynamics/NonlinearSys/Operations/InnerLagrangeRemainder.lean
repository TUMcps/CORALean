module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `innerLagrangeRemainder`, the Lagrange remainder of the inner algorithm

(9) of [1]: the interval `[-l̂, l̂]` that encloses the Lagrange remainder of `f`'s linearization at
`x*` over `X`, `l̂⁽ⁱ⁾ = ½ max|x - x*|ᵀ max D²f⁽ⁱ⁾ max|x - x*|`, the maxima over `X` taken
entrywise, with absolute values on the Hessian's entries. Line 12 of [1, Alg. 1] evaluates it on
the box (25) of the time-interval set.

## Inputs
* `f` – vector field
* `xstar` – linearization point
* `X` – region

## Output
* the interval `[-l̂, l̂]`

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Set

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- (9) of [1]: the Lagrange remainder of `f` at `x*` over `X`, `[-l̂, l̂]` with
`l̂⁽ⁱ⁾ = ½ max|x - x*|ᵀ max D²f⁽ⁱ⁾ max|x - x*|`. -/
noncomputable def NonlinearSys.innerLagrangeRemainder (f : Vec ℝ n → Vec ℝ n) (xstar : Vec ℝ n)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  -- (9) max_{x∈X} |x - x*|
  let γ : Vec ℝ n := fun j => ⨆ x ∈ X, |x j - xstar j|
  -- (9) max_{ζ∈X} D²f⁽ⁱ⁾(ζ)
  let H : Fin n → Mat ℝ n n := fun i j k =>
    ⨆ ζ ∈ X, |fderiv ℝ (fderiv ℝ f) ζ (Pi.single j 1) (Pi.single k 1) i|
  -- (9) l̂⁽ⁱ⁾ = ½ γᵀ H⁽ⁱ⁾ γ
  let l : Vec ℝ n := fun i => γ ⬝ᵥ (H i *ᵥ γ) / 2
  -- (9) L̂ = [-l̂, l̂]
  Icc (-l) l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
