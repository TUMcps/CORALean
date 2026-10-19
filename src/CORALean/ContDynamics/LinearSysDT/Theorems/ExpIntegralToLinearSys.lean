module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq
public import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys

@[expose] public section

/-!
# What the converted system holds over a step is the discrete one's input

With `e^L = A_d`, `dt ≠ 0` and `A_d - I` regular, `∫₀^dt e^{Aσ}dσ` applied to the converted `B`
(and to `c`, and to `E`) is the original `B` (`c`, `E`): the input that a step of the
converted system accumulates is the discrete one's, as [1] intends. Only for a regular
`A_d - I`; where `linsolve` fails CORA falls back on a numerical fit.

## References

* [1] `contDynamics/@linearSysDT/linearSys.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.expIntegral_toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n)
    (hdt : sys.dt ≠ 0) (hL : exp L = sys.A) (hM : IsUnit (sys.A - 1).det) : -- --- CONCL ---
    Real.MatExp.expIntegral (sys.dt⁻¹ • L) sys.dt * (sys.toLinearSys L).B = sys.B ∧
      Real.MatExp.expIntegral (sys.dt⁻¹ • L) sys.dt *ᵥ (sys.toLinearSys L).c = sys.c ∧
      Real.MatExp.expIntegral (sys.dt⁻¹ • L) sys.dt * (sys.toLinearSys L).E
        = sys.E := by -- --- PROOF ---
  set Ac : Mat ℝ n n := sys.dt⁻¹ • L with hAc
  set I : Mat ℝ n n := Real.MatExp.expIntegral Ac sys.dt with hI
  -- `A_d - 1 = Ac · I`, and a regular product has regular factors
  have hexp : exp (sys.dt • Ac) = sys.A := by
    rw [hAc, smul_smul, mul_inv_cancel₀ hdt, one_smul, hL]
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
  · show I * ((sys.A - 1)⁻¹ * (Ac * sys.B)) = sys.B
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hkey, Matrix.one_mul]
  · show I *ᵥ ((sys.A - 1)⁻¹ *ᵥ (Ac *ᵥ sys.c)) = sys.c
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hkey, Matrix.one_mulVec]
  · show I * ((sys.A - 1)⁻¹ * (Ac * sys.E)) = sys.E
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hkey, Matrix.one_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
