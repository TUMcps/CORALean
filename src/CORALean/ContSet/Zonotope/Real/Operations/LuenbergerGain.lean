module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.luenbergerGain`

The set-propagation observer's gain of [1, Prop. 2], the minimizer of the Frobenius norm of
`Ḡ` in `Zonotope.luenbergerUpdate`: `Λ = F Ĝ Ĝᵀ Γᵀ (Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ)⁻¹` Eq. 31 of
[1, Prop. 2], for the zonotope `⟨ĉ, Ĝ⟩`, the stacked measurement matrix `Γ` and the
measurement-noise generators `R`. `Ĝ` is the matrix of the generator columns; the inverse is
Mathlib's, `0` where `Γ Ĝ Ĝᵀ Γᵀ + R Rᵀ` is singular.

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

noncomputable def Zonotope.luenbergerGain (F : Mat ℝ n n) (Γ : Mat ℝ p n) (R : Mat ℝ p nr)
    (X : Zonotope (Vec ℝ n)) : Mat ℝ n p :=
  let Ĝ : Mat ℝ n X.h := Matrix.of fun i j => X.G j i              -- the generator matrix Ĝ
  F * Ĝ * Ĝᵀ * Γᵀ * (Γ * Ĝ * Ĝᵀ * Γᵀ + R * Rᵀ)⁻¹                  -- Eq. 31

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
