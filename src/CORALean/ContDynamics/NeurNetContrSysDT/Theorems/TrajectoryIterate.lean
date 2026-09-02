import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# A closed-loop run is an orbit

The controller is a function, so the loop is deterministic and `Trajectory`
carries no information beyond `x 0 ∈ R₀`: every run is the orbit of `map`, every
point of `R₀` starts one, and two runs agreeing at step zero agree everywhere.
Stated rather than left implied, because it is what makes the reachability
guarantee weaker than it looks — a set of runs here is a set of initial states,
and the enclosure is still loose, `reach` pairing each state with every input
rather than with its own.

Nothing downstream uses these. They are here so that the determinism is a
theorem rather than a remark.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

theorem NeurNetContrSysDT.Trajectory.eq_iterate {sys : NeurNetContrSysDT 𝕋 S n} {R₀ : S n}
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ x) (k : ℕ) :
    x k = sys.map^[k] (x 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, traj.step k]
    rfl

/-- Every point of `R₀` starts a run, so the runs of a closed loop are exactly
its initial states. -/
theorem NeurNetContrSysDT.trajectory_iterate (sys : NeurNetContrSysDT 𝕋 S n) {R₀ : S n}
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) :
    sys.Trajectory R₀ (fun k => sys.map^[k] x₀) where
  init := hx₀
  step k := Function.iterate_succ_apply' sys.map k x₀

/-- Determinism, in the form it is normally wanted: the initial state settles
the run, whichever initial sets the two runs were taken from. -/
theorem NeurNetContrSysDT.Trajectory.eq_of_init {sys : NeurNetContrSysDT 𝕋 S n} {R₀ R₁ : S n}
    {x y : ℕ → Vec ℝ n} (hx : sys.Trajectory R₀ x) (hy : sys.Trajectory R₁ y)
    (h : x 0 = y 0) : x = y := by
  funext k
  rw [hx.eq_iterate k, hy.eq_iterate k, h]

end CORALean.Real
