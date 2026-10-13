module

public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec

@[expose] public section

/-!
# What a constant input contributes over a step, in closed form

`expIntegral_mulVec` reads `∫₀ᵗ e^{Aσ}v dσ`, where a run's input meets the
propagator `e^{A(t-s)}` instead; the substitution `σ = t - s` is the whole
difference. So a constant input over `[0,t]` contributes exactly
`(∫₀ᵗ e^{Aσ}dσ)v`, [2, Eq. 5]'s `Γ(t)u_c` and [3, Eq. 12]'s `R_con`, with no matrix inverse
anywhere (`expIntegral_eq_inv_mul` brings one in for invertible `A`) — which is what lets an
input set be split into a constant and a remainder holding the origin.

Stated apart from either caller: the point-matrix split of [1, Alg. 3] and the
interval-matrix one of [1, Alg. 4] both need it, and it is about `MatExp`
alone — no system and no input set enter.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
* [3] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- `expIntegral_mulVec` carries the whole exponential series through the substitution
/-- What a constant input contributes over `[0,t]`, in closed form. -/
theorem Real.MatExp.expIntegral_constInput (A : Mat ℝ n n) (v : Vec ℝ n) {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ v) = Real.MatExp.expIntegral A t *ᵥ v := by
  rw [Real.MatExp.expIntegral_mulVec A v ht]
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
    (fun σ : ℝ => exp (σ • A) *ᵥ v) t
  simpa using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
