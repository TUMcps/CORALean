import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Two-input continuous runs: input and disturbance kept apart

`Trajectory` carries one signal `u`. [1, Def. 6] and [1, Def. 7] need a second,
independently-quantified one, `w`: `∀u(·)∈U ∃w(·)∈W` and `∃u(·)∈U ∀w(·)∈W`
cannot be built from one `Trajectory` folding the two together. So this is a
structure of its own over `ẋ = Ax + u + w`, a Carathéodory run as `Trajectory`
is: `x t = x 0 + ∫₀ᵗ (A x + u + w)`, so a run whose input or disturbance jumps
still counts. That matters for [1, Prop. 3] and [1, Prop. 5], whose right-hand
sides range over every point the particular solutions `Z_U(t)`, `Z_W(t)` hold,
and those are integrals of merely measurable signals.

`measInput`/`measDisturbance` are each signal's own regularity, `cont` the
continuity `Trajectory.cont` is. No `init`/`R₀`: Def. 6 and Def. 7 test one
starting point, which their own definitions pin, the way `reachSet` pins
`x t = y` outside `Trajectory`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory intervalIntegral

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A run under an input `u` and a disturbance `w`, each admissible and
measurable on `T`, with the flow stated as an integral equation. -/
structure LinearSys.PerturbedTrajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (U W : S n)
    (x u w : ℝ → Vec ℝ n) : Prop where
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  disturbance (t : ℝ) (ht : t ∈ T) : w t ∈ construct W
  measInput : AEStronglyMeasurable u (volume.restrict T)
  measDisturbance : AEStronglyMeasurable w (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) :
    x t = x 0 + ∫ s in (0:ℝ)..t, (toRealMat sys.A *ᵥ x s + u s + w s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
