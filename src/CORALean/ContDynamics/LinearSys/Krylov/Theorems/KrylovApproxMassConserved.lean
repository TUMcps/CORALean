module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

/-!
# The Krylov approximation of a unitary evolution conserves mass

[1, Eq. 8.3]: for `σ = -i` and Hermitian `A`, `T_m` is Hermitian, and with `‖v‖₂ = 1`,
`V_m*V_m = I`: `‖S_m(t)v‖₂ = ‖V_me^{-itT_m}e₁‖₂ = 1`. `e^{-itT_m}` is unitary,
`(e^{-itT_m})* = e^{itT_m}` commuting with `e^{-itT_m}`, and `V_m` keeps the norm. Stated for the
squared norm `y*y`; (8.3) prints its middle term `e₁*e^{itT_m}V_m*V_me^{-itT_m}e₁`, which is the
squared norm too.

## Inputs
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `t` – time

## Hypotheses
* `hT` – Hessenberg matrix Hermitian
* `hV` – basis has orthonormal columns

## Conclusion
* the Krylov approximation of the unitary evolution has unit norm

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 8.3]: `‖V_me^{-itT_m}e₁‖₂² = 1` for Hermitian `T_m` and `V_m*V_m = I`, here with
`m + 1` columns. -/
theorem Krylov.krylovApprox_mass_conserved (V : Mat ℂ n (m + 1)) (T : Mat ℂ (m + 1) (m + 1))
    (hT : Tᴴ = T) (hV : Vᴴ * V = 1) (t : ℝ) : -- --- CONCL ---
    let y := V *ᵥ (exp ((-Complex.I * t) • T) *ᵥ Pi.single 0 1)
    star y ⬝ᵥ y = 1 := by -- --- PROOF ---
  intro y
  set X : Mat ℂ (m + 1) (m + 1) := (-Complex.I * t) • T with hX
  -- `X* = -X`, so `(e^X)* e^X = e^{-X + X} = I`
  have hXs : Xᴴ = -X := by
    rw [hX, conjTranspose_smul, hT, star_mul', star_neg, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, ← neg_smul, neg_mul]
  have hU : (exp X)ᴴ * exp X = 1 := by
    rw [← Matrix.exp_conjTranspose, hXs, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left
      (Commute.refl X)), neg_add_cancel, exp_zero]
  -- `y*y = e₁*(e^X)*V*V e^X e₁ = e₁*e₁`
  simp only [y]
  rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, ← hX,
    star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
