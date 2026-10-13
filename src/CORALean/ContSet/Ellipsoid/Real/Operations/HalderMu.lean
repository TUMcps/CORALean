import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderElemSymm

/-!
# The coefficients of Halder's polynomial

The `µᵣ := (d − r) eᵣ − (r − 1) eᵣ₋₁` of [1, Eq. 23], with `eᵣ` the elementary symmetric
polynomials of `1/λᵢ`. Lemma 2 and Corollary 1 of the paper claim that `µ₁, …, µ_{d−1}` are
strictly increasing and positive; `not_halderMu_strictly_increasing` and
`not_halderMu_positive` show that neither holds.

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

variable {ι : Type*} [Fintype ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `µᵣ = (d − r) eᵣ − (r − 1) eᵣ₋₁` of [1, Eq. 23], for `eᵣ` of the reciprocals `1/λᵢ`. -/
noncomputable def Ellipsoid.halderMu (lam : ι → ℝ) (r : ℕ) : ℝ :=
  ((Fintype.card ι : ℝ) - r) * Ellipsoid.halderElemSymm (fun i => 1 / lam i) r
    - ((r : ℝ) - 1) * Ellipsoid.halderElemSymm (fun i => 1 / lam i) (r - 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
