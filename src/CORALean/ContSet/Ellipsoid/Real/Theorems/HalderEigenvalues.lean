import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderDiagonalizable

/-!
# The ratio of two shape matrices has positive eigenvalues

[1, Prop. 1]: for positive-definite `Q₁` and `Q₂`, `R = Q₁⁻¹ Q₂` is diagonalizable, and its
eigenvalues are positive. It is [1, Lemma 1] at `M₁ = Q₁⁻¹`, which is positive definite when
`Q₁` is; the positivity of the eigenvalues, which the printed proof reads off the spectrum
of `Q₂^(1/2) Q₁⁻¹ Q₂^(1/2)`, comes with the construction there.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `Q₁⁻¹ Q₂ = S diag(λ) T`, `S T = 1`, with every `λᵢ` positive. -/
theorem Ellipsoid.halder_eigenvalues {Q₁ Q₂ : Matrix n n ℝ} (h₁ : Q₁.PosDef)
    (h₂ : Q₂.PosDef) :
    ∃ (S T : Matrix n n ℝ) (lam : n → ℝ), S * T = 1 ∧ T * S = 1 ∧
      Q₁⁻¹ * Q₂ = S * diagonal lam * T ∧ ∀ i, 0 < lam i := by
  obtain ⟨S, T, d, hST, hTS, hprod, hpos⟩ :=
    Ellipsoid.halder_diagonalizable h₁.inv h₂.isHermitian
  exact ⟨S, T, d, hST, hTS, hprod, hpos h₂⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
