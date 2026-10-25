module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# The standard Gaussian mass of a cube

The standard Gaussian on `ℝⁿ` gives the cube `[-m, m]ⁿ` the mass `P[-m ≤ N(0, 1) ≤ m]ⁿ`: its
coordinates are independent standard Gaussians. [1, Prop. 2]'s proof, "choosing `n` generators,
the event that a value lies in the set spanned by them is `erf(m/√2)ⁿ`", at the level of the
coefficients; `erf(m/√2)` is the one-dimensional mass, which [1] quotes as well known.

## Inputs
* `m` – real number

## Hypotheses
* none

## Conclusion
* the standard Gaussian mass of the cube `[-m, m]ⁿ` is the one-dimensional mass to the power `n`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem stdGaussian_cube (m : ℝ) : -- --- CONCL ---
    stdGaussian (EuclideanSpace ℝ (Fin n)) {β | ∀ i, ofLp β i ∈ Set.Icc (-m) m}
      = (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n := by -- --- PROOF ---
  have hmeas : MeasurableSet {β : EuclideanSpace ℝ (Fin n) | ∀ i, ofLp β i ∈ Set.Icc (-m) m} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (by fun_prop)
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hmeas]
  -- the cube is a product of intervals
  have : (toLp 2) ⁻¹' {β : EuclideanSpace ℝ (Fin n) | ∀ i, ofLp β i ∈ Set.Icc (-m) m}
      = Set.univ.pi (fun _ : Fin n => Set.Icc (-m) m) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rw [this, Measure.pi_pi]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
