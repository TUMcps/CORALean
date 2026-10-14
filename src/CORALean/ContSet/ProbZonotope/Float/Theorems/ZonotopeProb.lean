module

public import CORALean.ContSet.ProbZonotope.Float.Theorems.ZonotopeOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ZonotopeProb
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# Every law of a float probabilistic zonotope puts `erf(m/√2)ⁿ` on its float confidence zonotope

[1, Prop. 2] as `ProbZonotope.zonotope_prob` has it at the exact layer, for the float
`ProbZonotope.zonotope`: whatever the mean `μ` in the mean zonotope and the positive semidefinite
covariance `Σ` in the interval, `N(μ, Σ)` puts at least `P[-m ≤ N(0, 1) ≤ m]ⁿ` on the result, for
`0 < m` up to the float `m`. The exact set for the point mean `μ` lies in it (`zonotope_outer`), so
the exact probability carries over. Outer: the result is a diagonal-generator box around the mean
zonotope, larger than the exact confidence set, which CORA's eigen generators span.

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

theorem ProbZonotope.zonotope_prob (p : ℕ) (P : ProbZonotope 𝕋 n) (M : 𝕋) {m : ℝ} (hm : 0 < m)
    (hmM : m ≤ toReal M) {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : ν ∈ P.laws) :
    (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n
      ≤ ν (toLp 2 '' (P.zonotope p M).construct) := by -- --- PROOF ---
  obtain ⟨μ, hμ, S, hS, hpsd, rfl⟩ := hν
  -- the exact probabilistic zonotope with the point mean `μ`
  set Q : Real.ProbZonotope n := ⟨⟨0, μ, fun j => j.elim0⟩, S⟩ with hQ
  have hμQ : μ ∈ Q.Z.construct :=
    Real.Zonotope.mem_construct_iff.mpr ⟨fun j => j.elim0, fun j => j.elim0, fun i => by simp [hQ]⟩
  exact le_trans (Real.ProbZonotope.zonotope_prob Q hpsd hm ⟨μ, hμQ, rfl⟩)
    (measure_mono (Set.image_mono (ProbZonotope.zonotope_outer p P M hμ hS hpsd hm.le hmM)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
