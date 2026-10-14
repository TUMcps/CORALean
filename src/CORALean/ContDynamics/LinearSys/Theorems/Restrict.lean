module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# A trajectory restricts to any smaller time domain

Every field but `meas` restricts pointwise, the integral equation being anchored
at `0` and not at `T`; `meas` restricts with the measure. This is what makes the
domain a parameter worth having —
a run over all forward time is a run over `[0, τ]`, so a one-step guarantee
applies to it without restating the hypotheses.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {sys : LinearSys 𝕋 n} {T T' : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `T` is a run on any smaller domain. -/
theorem LinearSys.CanonicalTrajectory.restrict (traj : sys.CanonicalTrajectory T R₀ U x u)
    (hT : T' ⊆ T) :
    sys.CanonicalTrajectory T' R₀ U x u where
  init := traj.init
  input t ht := traj.input t (hT ht)
  meas := traj.meas.mono_measure (MeasureTheory.Measure.restrict_mono hT le_rfl)
  cont := traj.cont.mono hT
  flow t ht := traj.flow t (hT ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
