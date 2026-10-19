module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryTimeIntervalStepOuter
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A time-varying run at a matrix zonotope, in the step of its box

What `'varParam'` gets at `𝕄𝒵`: a run drawing a fresh member of the matrix
zonotope at every instant draws one of its box too (`Zonotope.interval_contains`),
so it is an input-free run of the interval system, and the box's own step holds it
(`IsTrajectory.timeIntervalStep_outer`).

Not the matrix-zonotope step `timeIntervalStepZono`, which only
`IsConstTrajectory.timeIntervalZono_outer` reaches. The Peano–Baker averaging would
carry over — a matrix-zonotope power holds products of different members and is
closed and convex — but is not done here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run at a matrix zonotope is, at every time of the
step, in the time-interval step of the zonotope's box. -/
theorem LinParamSys.IsCanonicalTrajectory.timeIntervalStep_interval_outer {sys : LinParamSys 𝕄𝒵 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u A) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 r, u s = 0) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    x t ∈ construct
      ((LinParamSys.canonical sys.A.interval : LinParamSys ℐ n).timeIntervalStep r (m + 2)
        R₀) := by -- --- PROOF ---
  have trajI : (LinParamSys.canonical sys.A.interval : LinParamSys ℐ n).IsCanonicalTrajectory T R₀ U
      x u A :=
    ⟨traj.init, traj.input, fun s hs => Zonotope.interval_contains _ (traj.param s hs),
      traj.meas, traj.measParam, traj.cont, traj.flow⟩
  exact trajI.timeIntervalStep_outer hr hT hu hε ht0 htr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
