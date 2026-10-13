module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq
public import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys

@[expose] public section

/-!
# What the converted system holds over a step is the discrete one's input

With `e^L = A_d`, `Δt ≠ 0` and `A_d - I` regular, `∫₀^Δt e^{Aσ}dσ` applied to the converted `B`
(and to `c`, and to `E`) is the original `B` (`c`, `E`): the input that a step of the
converted system accumulates is the discrete one's, as [1] intends. Only for a regular
`A_d - I`; where `linsolve` fails CORA falls back on a numerical fit.

## References

* [1] `contDynamics/@linearSysDT/linearSys.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.expIntegral_toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n) {Δt : ℝ}
    (hΔt : Δt ≠ 0) (hL : exp L = sys.A) (hM : IsUnit (sys.A - 1).det) (B : Mat ℝ n m)
    (c : Vec ℝ n) (E : Mat ℝ n q) :
    Real.MatExp.expIntegral (Δt⁻¹ • L) Δt * (sys.toLinearSys L Δt B c E).2.1 = B ∧
      Real.MatExp.expIntegral (Δt⁻¹ • L) Δt *ᵥ (sys.toLinearSys L Δt B c E).2.2.1 = c ∧
      Real.MatExp.expIntegral (Δt⁻¹ • L) Δt * (sys.toLinearSys L Δt B c E).2.2.2
        = E := by -- --- PROOF ---
  set Ac : Mat ℝ n n := Δt⁻¹ • L with hAc
  set I : Mat ℝ n n := Real.MatExp.expIntegral Ac Δt with hI
  -- `A_d - 1 = Ac · I`, and a regular product has regular factors
  have hexp : exp (Δt • Ac) = sys.A := by
    rw [hAc, smul_smul, mul_inv_cancel₀ hΔt, one_smul, hL]
  have hprod : sys.A - 1 = Ac * I := by
    rw [hI, Real.MatExp.mul_expIntegral, hexp]
  have hdet : IsUnit (Ac.det * I.det) := by rw [← Matrix.det_mul, ← hprod]; exact hM
  have hAcu : IsUnit Ac.det := isUnit_of_mul_isUnit_left hdet
  have hIu : IsUnit I.det := isUnit_of_mul_isUnit_right hdet
  -- `I (A_d - 1)⁻¹ Ac = 1`, so every one of the three is undone
  have hkey : I * (sys.A - 1)⁻¹ * Ac = 1 := by
    rw [hprod, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc I⁻¹ Ac⁻¹ Ac,
      Matrix.nonsing_inv_mul _ hAcu, Matrix.mul_one, Matrix.mul_nonsing_inv _ hIu]
  refine ⟨?_, ?_, ?_⟩
  · simp only [LinearSysDT.toLinearSys]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hkey, Matrix.one_mul]
  · simp only [LinearSysDT.toLinearSys]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show I * (sys.A - 1)⁻¹ * (Δt⁻¹ • L) = 1 from hkey, Matrix.one_mulVec]
  · simp only [LinearSysDT.toLinearSys]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hkey, Matrix.one_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
