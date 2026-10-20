module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.stripGain`

The strip-based observer's gain of [1, Alg. 1] Step 1, the minimizer of the Frobenius norm of
`Ḡ`, in closed form [1, Eq. 38]: `Λₛ = Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹` for the
predicted zonotope `⟨ĉ, Ĝ⟩`, the stacked measurement matrix `Γ` and the measurement-noise
generators `R`. `Ĝ` is the matrix of the generator columns; the inverse is Mathlib's, `0` where
`Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ` is singular.

## Inputs
* `Γ` – stacked measurement matrix
* `R` – measurement-noise generators
* `X` – zonotope

## Output
* gain minimizing the generator Frobenius norm

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p nr : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.stripGain (Γ : Mat ℝ p n) (R : Mat ℝ p nr) (X : Zonotope (Vec ℝ n)) :
    Mat ℝ n p :=
  let Ĝ : Mat ℝ n X.h := Matrix.of fun i j => X.G j i              -- the generator matrix Ĝ
  Ĝ * Ĝᵀ * Γᵀ * (Γ * Ĝ * Ĝᵀ * Γᵀ + R * Rᵀ)⁻¹                      -- Eq. 38

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
