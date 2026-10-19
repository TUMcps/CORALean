module

public import CORALean.ContDynamics.LinProbSys.LinProbSys

@[expose] public section

/-!
# A run's state is a random variable

At every time `t ≥ 0` of `T` the state `x t` of a `LinProbSys.IsTrajectory` is almost everywhere
measurable, and `P` is a probability measure: `law` says that the image of `P` under `x t` is a
Gaussian, a probability measure, and the image under a map that is not almost everywhere
measurable is `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory ProbabilityTheory WithLp

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state at a time `t ≥ 0` of `T` is almost everywhere measurable, and `P` a probability
measure. -/
theorem LinProbSys.IsTrajectory.aemeasurable {sys : LinProbSys n m} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : S n} {U : S m} {x₀ : Vec ℝ n}
    {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n} (traj : sys.IsTrajectory P T X₀ U x₀ u x) {t : ℝ}
    (ht : t ∈ T) (h0 : 0 ≤ t) : -- --- STMT ---
    AEMeasurable (fun ω => toLp 2 (x t ω)) P ∧ IsProbabilityMeasure P := by -- --- PROOF ---
  have hlaw := traj.law t ht h0
  -- the image is a probability measure, so the map is measurable
  have hmeas : AEMeasurable (fun ω => toLp 2 (x t ω)) P := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hlaw
    have := measure_univ (μ := multivariateGaussian
      (toLp 2 (NormedSpace.exp (t • sys.A) *ᵥ x₀ + ∫ s in (0:ℝ)..t,
        NormedSpace.exp ((t - s) • sys.A) *ᵥ (sys.B *ᵥ u s))) (noiseCovariance sys.A sys.C t))
    rw [← hlaw] at this
    simp at this
  refine ⟨hmeas, ⟨?_⟩⟩
  -- the image of `P` has the mass of `P`
  have h := Measure.map_apply_of_aemeasurable hmeas MeasurableSet.univ
  rw [hlaw, measure_univ, Set.preimage_univ] at h
  exact h.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
