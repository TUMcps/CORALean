module

public import CORALean.ContSet.ProbZonotope.Float.Theorems.ZonotopeProb
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# Every law of a float probabilistic zonotope puts `erf(m/√2)ⁿ` on its float interval

The float `ProbZonotope.interval` is the interval hull of `ProbZonotope.zonotope`, so
`ProbZonotope.zonotope_prob` ([1, Prop. 2]) carries over (`Zonotope.interval_contains`): whatever
the mean in the mean zonotope and the positive semidefinite covariance in the interval, the law puts
at least `P[-m ≤ N(0, 1) ≤ m]ⁿ` on the box, for `0 < m` up to the float `m`. Outer: the box contains
the confidence set and is not equal to it.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory WithLp FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.interval_prob (p : ℕ) (P : ProbZonotope 𝕋 n) (M : 𝕋) {m : ℝ} (hm : 0 < m)
    (hmM : m ≤ toReal M) {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : ν ∈ P.laws) :
    (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n
      ≤ ν (toLp 2 '' (P.interval p M).construct) :=
  (ProbZonotope.zonotope_prob p P M hm hmM hν).trans
    (measure_mono (Set.image_mono (P.zonotope p M).interval_contains))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
