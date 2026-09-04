import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter

/-!
# A trajectory stays in the step enclosure, inputs and all

The closed form splits a run into what the initial set carries and what the
inputs contributed, and the two are enclosed separately: `timeIntervalStep` for
the first, a set the caller supplies for the second.

That input enclosure is a hypothesis, discharged by
`timeInterval_outer_inputSolution`: `t` ranges over the whole step, so one set
has to cover every `t` at once, which is Prop. 3.3 and costs `0 ∈ U` on top of
what the sampled version needs.

Integrability is not a hypothesis — `InputIntegrable` derives it from `U` being
bounded.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
-- the conclusion is a four-way `plus` of `Mtimes` results, elaborated at `ℐ` and `Mat ℝ`
set_option maxHeartbeats 1000000 in
/-- One step and nothing more: the domain has to cover `[0, r]` only, which is
what makes this a statement about a hybrid location or a single linearization
step rather than about a whole run. -/
theorem LinearSys.Trajectory.timeInterval_outer {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) ∈ construct Ud) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀) Ud) := by
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hvoc := traj.variation_of_constants hTt ht0
    (traj.intervalIntegrable_input hTt ht0 hU)
  rw [sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStep_outer hr hε R₀ ht0 htr
    (Set.mem_image_of_mem _ traj.init)

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- The same, with the input set named rather than assumed. `0 ∈ U` is what buys
a single enclosure for the whole step; everything else is a property of `U` that
a representation supplies. -/
theorem LinearSys.Trajectory.timeInterval_outer_inputSolution {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer hr hT hε ht0 htr hbdd
    (traj.inputSolution_timeInterval_outer hr hT (m + 2) hε hconv hclosed hbdd
      hRconv hRclosed hRbdd h0 ht0 htr)

end CORALean.Real
