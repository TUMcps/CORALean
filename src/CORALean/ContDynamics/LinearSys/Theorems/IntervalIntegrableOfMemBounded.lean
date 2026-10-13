module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# A bounded, measurable signal is interval integrable

The one fact every flow equation here needs of its input and of its
disturbance, and the only place a representation enters an integrability
argument: `construct U` is bounded, `u` stays inside it on the window, so the
integrand is dominated by a constant over a finite measure.

Stated for a bare signal rather than for a run, since the two-signal flow of
`PerturbedTrajectory` needs it once per signal and neither of those is
the input of a `Trajectory` on its own.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A signal staying in a bounded set on `[0, t]` and measurable there is
interval integrable over that window. -/
theorem intervalIntegrable_of_mem_bounded {U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) :
    IntervalIntegrable u volume 0 t := by -- --- PROOF ---
  obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  refine ⟨hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl),
    HasFiniteIntegral.restrict_of_bounded (C := Cu) measure_Ioc_lt_top ?_⟩
  exact (ae_restrict_iff' measurableSet_Ioc).mpr
    (Filter.Eventually.of_forall fun s hs => hCu _ (hu s ⟨hs.1.le, hs.2⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
