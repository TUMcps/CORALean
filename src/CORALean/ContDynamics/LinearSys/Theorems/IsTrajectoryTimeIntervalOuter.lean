module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterAt
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

@[expose] public section

/-!
# A trajectory stays in the step enclosure, inputs and all

The closed form splits a run into what the initial set carries and what the inputs contributed, and
the two are enclosed separately: `timeInterval` for the first, a set the caller supplies for the
second, a hypothesis that `TimeIntervalOuterInputSolution` discharges with
`timeInterval_outer_inputSolution`. Integrability is not a hypothesis: `InputIntegrable` derives it
from `U` being bounded.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- One step and nothing more: the domain has to cover `[0, r]` only, which is
what makes this a statement about a hybrid location or a single linearization
step rather than about a whole run. -/
theorem LinearSys.IsCanonicalTrajectory.timeInterval_outer {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.IsCanonicalTrajectory T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) ∈ construct Ud)
    : -- --- CONCL ---
    x t ∈ construct (Plus.plus (sys.timeInterval r (m + 2) R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hvoc := traj.variation_of_constants hTt le_rfl ht0
    hU
  rw [sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeInterval_outer_at hr hε R₀ ht0 htr
    (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
