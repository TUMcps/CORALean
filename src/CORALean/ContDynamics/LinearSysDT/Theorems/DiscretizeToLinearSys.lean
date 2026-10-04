import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys

/-!
# Discretizing the converted system gives the system back

With `e^L = A_d` and `Δt ≠ 0`, the system `linearSys(linsysDT)` returns has `e^{Δt A} = A_d`:
sampling it at `Δt` is the original. [1] holds for any `L` that is an exponential logarithm,
the principal one or not; no claim that CORA's `logm` is the only one.

## References

* [1] `contDynamics/@linearSysDT/linearSys.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.discretize_toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n) {Δt : ℝ}
    (hΔt : Δt ≠ 0) (hL : exp L = sys.A) (B : Mat ℝ n m) (c : Vec ℝ n) (E : Mat ℝ n q) :
    (sys.toLinearSys L Δt B c E).1.discretize Δt = sys := by -- --- PROOF ---
  -- the scaling cancels: `Δt • (Δt⁻¹ • L) = L`
  obtain ⟨A⟩ := sys
  simp only [LinearSys.discretize, LinearSysDT.toLinearSys, Scalar.toRealMat_real,
    smul_smul, mul_inv_cancel₀ hΔt, one_smul] at hL ⊢
  rw [hL]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
