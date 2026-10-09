import CORALean.ContSet.ProbZonotope.Real.Operations.Interval
import CORALean.ContSet.ProbZonotope.Real.Theorems.ZonotopeProb

/-!
# Every law of a probabilistic zonotope puts `erf(m/√2)ⁿ` on its interval

The box `ProbZonotope.interval` contains the confidence set `zonotope(probZ, m)` (the interval
hull of a zonotope), so [1, Prop. 2] as `zonotope_prob` has it carries over: whatever the mean
`μ ∈ Z`, `N(μ, Σ)` puts at least `P[-m ≤ N(0, 1) ≤ m]ⁿ` on it. Outer: the box is an
overapproximation of the confidence set, not equal to it.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.interval_prob (P : ProbZonotope n) (hP : P.cov.PosSemidef) {m : ℝ}
    (hm : 0 < m) {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : ν ∈ P.laws) :
    (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n ≤ ν (toLp 2 '' (P.interval m).construct) :=
  (P.zonotope_prob hP hm hν).trans
    (measure_mono (Set.image_mono (P.zonotope m).interval_contains))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
