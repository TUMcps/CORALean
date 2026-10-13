import CORALean.Global.Tensor
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# `exp(-‖v‖²/2)` is integrable on Euclidean space

What normalizes the standard Gaussian density, read off Mathlib's complex Gaussian integrability
by taking norms. Used for [1, Prop. 1]'s density and for its counterexample.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory Complex
open scoped RealInnerProductSpace

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem integrable_exp_neg_norm_sq_half :
    Integrable (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-‖v‖ ^ 2 / 2)) := by -- --- PROOF ---
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin n)) (b := (1 / 2 : ℂ)) (by norm_num) 0 0).norm
  have h' : (fun v : EuclideanSpace ℝ (Fin n) =>
      ‖cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + 0 * ⟪(0 : EuclideanSpace ℝ (Fin n)), v⟫)‖)
      = fun v => Real.exp (-‖v‖ ^ 2 / 2) := by
    funext v
    rw [Complex.norm_exp]
    congr 1
    simp
    norm_cast
    ring
  rwa [h'] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
