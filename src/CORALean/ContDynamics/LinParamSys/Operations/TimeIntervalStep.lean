module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# One step of the homogeneous flow at a set-valued system matrix, as a set

`LinearSys.timeIntervalStep` with both matrices replaced by the sets that hold
them: `e^{Ar}` by `expIntervalEnclosure` of the box `r • sys.A`, and `F` by
`intervalCorrectionMatrix`. Neither is computed at a member — a member is what a
`IsConstTrajectory` fixes and an implementation never sees.

At `ℐ`, not at any matrix representation: both enclosures are interval matrices,
and the step multiplies by them. `𝕄𝒵` would keep the correlations between a
matrix's entries through the powers, as `expMatZonoEnclosure` does, and needs
`intervalCorrectionMatrix`'s counterpart at a matrix zonotope, which is not
written.

The order `η` is a choice, sound at any value, subject to the same joint
condition on step and order the enclosures carry.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀`, over a whole step, with `A` ranging over
`sys.A` rather than fixed. -/
noncomputable def LinParamSys.timeIntervalStep (sys : LinParamSys ℐ n) (r : ℝ) (η : ℕ)
    (X₀ : S n) : S n :=
  LinComb.linComb X₀ (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.expIntervalEnclosure (Interval.smul r sys.A) η) X₀) ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalCorrectionMatrix sys.A r η) X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
