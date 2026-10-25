module

public import CORALean.NN.Layers.Definitions.PolySampling
public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# A concrete fit: least squares over the sample grid

CORA's default `poly_method`, [1, Alg. 1]'s line 7 "Polynomial Regression": sample the box at
`10 (n + 1)` points and take the degree-`n` polynomial minimising the squared residual there;
`taylor`, `bernstein` and `singh` are the alternatives, a precision question only. Nothing here
is proved and nothing here can be wrong: a relaxation's soundness quantifies over the
coefficients it is handed, so the fit is a heuristic input. Over ℝ alone, a linear solve being
nothing a machine scalar is asked for; the runnable relaxation takes its coefficients as data.
The normal equations rather than a decomposition, `Matrix.inv` being total: at a singular Gram
matrix it returns junk, the fit is a bad one, and the error bound absorbs it.

## Inputs
* `l` – lower end of the interval
* `u` – upper end of the interval
* `m` – number of sample intervals
* `n` – polynomial degree

## Output
* matrix of monomials at the sample points

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The design matrix of the fit: one row per sample of `[l, u]`, one column per monomial. -/
noncomputable def sampleVandermonde (l u : ℝ) (m n : ℕ) : Mat ℝ (m + 1) (n + 1) :=
  fun k i => sampleGrid l u m k ^ (i : ℕ)

/-- Least squares over the `m + 1` samples of `[l, u]`, through the normal equations. -/
noncomputable def leastSquaresFit (σ : ℝ → ℝ) (l u : ℝ) (m n : ℕ) : Fin (n + 1) → ℝ :=
  ((sampleVandermonde l u m n)ᵀ * sampleVandermonde l u m n)⁻¹
    *ᵥ ((sampleVandermonde l u m n)ᵀ *ᵥ fun k => σ (sampleGrid l u m k))

/-- CORA's default fit, at its sample count of `10 (n + 1)` points per box. -/
noncomputable def polyFit (σ : ℝ → ℝ) (n : ℕ) (l u : ℝ) : Fin (n + 1) → ℝ :=
  leastSquaresFit σ l u (10 * n + 9) n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
