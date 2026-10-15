module

public import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMemExpIntervalEnclosure

@[expose] public section

/-!
# Where an input-free time-varying run is at a time of its window

`Trajectory.exists_mem_expIntervalEnclosure` read at the sets: the box's
exponential enclosure over `t` times the initial set holds the run's state at
`t`. CORA's `'varParam'` homogeneous solution at a time point, the mapping matrix
of `priv_mappingMatrix` applied to the initial set; the same set
`LinParamSys.timeIntervalStep` starts from at `'constParam'`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run is, at every time `t` of its window, in the
box's exponential enclosure over `t` times the initial set. -/
theorem LinParamSys.CanonicalTrajectory.timePoint_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.CanonicalTrajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) (η : ℕ)
    (hε : ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) < 1) :
    x t ∈ construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.expIntervalEnclosure (Interval.smul t sys.A) η) R₀) := by -- --- PROOF ---
  obtain ⟨Φ, hΦ, hx⟩ := traj.exists_mem_expIntervalEnclosure ht hT hu η hε
  rw [hx]
  exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hΦ (Set.mem_image_of_mem _ traj.init))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
