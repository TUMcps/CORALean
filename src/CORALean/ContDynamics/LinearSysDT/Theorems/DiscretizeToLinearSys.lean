module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSysDT.Operations.ToLinearSys

@[expose] public section

/-!
# Discretizing the converted system gives the system back

With `e^L = A_d` and `dt ≠ 0`, the system `linearSys(linsysDT)` returns has `e^{dt A} = A_d`:
sampling it at `dt` gives the original state matrix. `discretize` returns the canonical form,
so `A` is what there is to compare. [1] holds for any `L` that is an exponential logarithm,
the principal one or not; no claim that CORA's `logm` is the only one.

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

theorem LinearSysDT.discretize_toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n)
    (hdt : sys.dt ≠ 0) (hL : exp L = sys.A) :
    ((sys.toLinearSys L).discretize sys.dt).A = sys.A := by
  -- the scaling cancels: `sys.dt • (sys.dt⁻¹ • L) = L`
  simp only [LinearSys.discretize, LinearSysDT.canonical, LinearSysDT.toLinearSys,
    Scalar.toRealMat_real, smul_smul, mul_inv_cancel₀ hdt, one_smul] at hL ⊢
  rw [hL]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
