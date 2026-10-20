module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# The derivative of `e^{sM}x` in the real time `s`, for a complex matrix

`d/ds e^{sM}x = Me^{sM}x`, the step of [1, Eq. 2.8] that makes the error `L_m(s)v` solve
`L' = σAL + D`: Mathlib's derivative of `s ↦ e^{sM}` in the normed algebra of complex
matrices over `ℝ`, carried through the continuous ℝ-linear map `B ↦ Bx`.

## Inputs
* `M` – complex matrix
* `x` – vector
* `s` – real time

## Hypotheses
* none

## Conclusion
* the exponential trajectory has the matrix times itself as derivative

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.8]'s step: `d/ds e^{sM}x = Me^{sM}x` for a complex matrix `M` and real `s`. -/
theorem Krylov.hasDerivAt_exp_smul_mulVec (M : Mat ℂ n n) (x : Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => exp (r • M) *ᵥ x) (M *ᵥ (exp (s • M) *ᵥ x)) s := by -- --- PROOF ---
  -- `B ↦ Bx` as a continuous ℝ-linear map
  let L : Mat ℂ n n →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun B => B *ᵥ x
      map_add' := fun B C => Matrix.add_mulVec B C x
      map_smul' := fun r B => by rw [Matrix.smul_mulVec, RingHom.id_apply] }
  have h := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M s)
  have h2 : HasDerivAt (fun r : ℝ => exp (r • M) *ᵥ x)
      ((LinearMap.toContinuousLinearMap L) (M * exp (s • M))) s := h
  refine h2.congr_deriv ?_
  show (M * exp (s • M)) *ᵥ x = _
  rw [Matrix.mulVec_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
