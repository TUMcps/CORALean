import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousPeanoBakerTerm

/-!
# The integrand of the next Peano–Baker term is integrable

Entry `(i, j)` of `A(σ) P_k(σ)` is a finite sum of an integrable entry of `A`
against a continuous one of `P_k` (`MatExp.continuous_peanoBakerTerm`), so it is
integrable over every bounded window — what each integral the series takes needs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.intervalIntegrable_mul_peanoBakerTerm {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) (k : ℕ)
    (i j : Fin n) (a b : ℝ) :
    IntervalIntegrable (fun σ => (A σ * MatExp.peanoBakerTerm A k σ) i j) volume a b := by
  simp only [Matrix.mul_apply]
  have h := IntervalIntegrable.sum Finset.univ fun l _ =>
    (hA i l a b).mul_continuousOn (MatExp.continuous_peanoBakerTerm hA k l j).continuousOn
  rwa [Finset.sum_fn] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
