import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A trajectory restricts to any smaller time domain

`HasDerivWithinAt.mono` is the whole content: a derivative within `T` is one
within every `T' ⊆ T`. This is what makes the domain a parameter worth having —
a run over all forward time is a run over `[0, τ]`, so a one-step guarantee
applies to it without restating the hypotheses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {sys : LinearSys 𝕋 n} {T T' : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}

/-- Every run on `T` is a run on any smaller domain. -/
theorem LinearSys.Trajectory.restrict (traj : sys.Trajectory T R₀ U x u) (hT : T' ⊆ T) :
    sys.Trajectory T' R₀ U x u where
  init := traj.init
  input t ht := traj.input t (hT ht)
  flow t ht := (traj.flow t (hT ht)).mono hT

end CORALean.Real
