module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# The substitution that cancels the dynamics

Along a solution, `e^{-As} x(s)` moves only as the input pushes it: the drift
term the product rule leaves behind is exactly what `A *ᵥ x(s)` cancels
against. Shared between `VariationOfConstants`, where it gives the closed
form outright, and `InputIntegrable`, where it says the integrand there is
itself a derivative.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem hasDerivWithinAt_expNeg_mulVec (A : Mat ℝ n n) (x u : ℝ → Vec ℝ n)
    (T : Set ℝ) (t : ℝ) (hx : HasDerivWithinAt x (A *ᵥ x t + u t) T t) :
    HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (exp ((-t) • A) *ᵥ u t)
      T t := by -- --- PROOF ---
  have hE : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-(exp ((-t) • A) * A)) t := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    simp only [smul_neg, ← neg_smul, mul_neg] at h
    exact h
  have hC : HasDerivWithinAt (fun s : ℝ => mulVecL (exp ((-s) • A)))
      (mulVecL (-(exp ((-t) • A) * A))) T t :=
    HasFDerivAt.comp_hasDerivWithinAt t (ContinuousLinearMap.hasFDerivAt mulVecL)
      hE.hasDerivWithinAt
  have key : mulVecL (-(exp ((-t) • A) * A)) (x t)
      + mulVecL (exp ((-t) • A)) (A *ᵥ x t + u t) = exp ((-t) • A) *ᵥ u t := by
    show (-(exp ((-t) • A) * A)) *ᵥ x t + exp ((-t) • A) *ᵥ (A *ᵥ x t + u t) = _
    rw [Matrix.neg_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  exact key ▸ HasDerivWithinAt.clm_apply hC hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
