module

public import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEq
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemExpIntervalEnclosureOfIntegral

@[expose] public section

/-!
# A time-varying run is mapped by a member of the box's exponential enclosure

CORA's `'varParam'` mapping matrix made sound for `Trajectory`, a fresh
`A t ∈ sys.A` at every instant: an input-free run reaches `x(t) = Φ x(0)` for some
`Φ ∈ expIntervalEnclosure (t • sys.A) η` — the interval matrix `expmIndMixed`
computes in `priv_mappingMatrix`, and the very one `'constParam'` already uses.
So the two readings need the same mapping matrix, where freezing one member and
paying the drift as input (`Trajectory.timeInterval_outer`) needs a wider set.

The run solves the integral equation at a measurable member of the box
(`Trajectory.exists_integral_eq`), and the Peano–Baker expansion of that equation
(`MatExp.exists_mem_expIntervalEnclosure_of_integral`) is the rest.

Input-free only, as CORA too splits the input off into `Rtrans` and the input
solution.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run, at a time `t` of its window, is its start
mapped by a member of the box's exponential enclosure over `t`. -/
theorem LinParamSys.Trajectory.exists_mem_expIntervalEnclosure {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) (η : ℕ)
    (hε : ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) < 1) :
    ∃ Φ ∈ construct (MatExp.expIntervalEnclosure (Interval.smul t sys.A) η),
      x t = Φ *ᵥ x 0 := by
  obtain ⟨Â, hÂi, hÂB, hx⟩ := traj.exists_integral_eq ht hT hu
  have hxc : ContinuousOn x (Set.Icc 0 t) := traj.cont.mono hT
  exact MatExp.exists_mem_expIntervalEnclosure_of_integral hÂi hÂB ht hxc hx η hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
