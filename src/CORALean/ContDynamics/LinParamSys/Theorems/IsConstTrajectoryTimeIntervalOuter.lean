module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

@[expose] public section

/-!
# A constant-parameter run stays in the step enclosure, inputs and all

`LinearSys.IsCanonicalTrajectory.timeInterval_outer` at `'constParam'`: the closed form
splits the run into what the initial set carries and what the inputs
contributed, and `toLinearSys` is what lets that closed form be used at all —
one matrix is fixed over the step, so `variation_of_constants` applies to it
unchanged.

The initial part is the box's `timeIntervalStep`, which knows no member. The
input part is a set the caller supplies, left open so that this file states the
homogeneous half alone; `timeInterval_outer_inputSolution` discharges `hUd`
with `sys.inputSolution`.

Integrability is not a hypothesis — `InputIntegrable` derives it from `U` being
bounded.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step and nothing more, at every matrix the system's set holds: the
domain has to cover `[0, r]` only. -/
theorem LinParamSys.IsCanonicalConstTrajectory.timeInterval_outer {sys : LinParamSys ℐ n}
    {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {r : ℝ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) ∈ construct Ud) : -- --- STMT ---
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have lin := traj.toLinearSys
  have hvoc := lin.variation_of_constants hTt le_rfl ht0 hU
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStep_outer hr hε R₀ traj.param ht0 htr
    (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
