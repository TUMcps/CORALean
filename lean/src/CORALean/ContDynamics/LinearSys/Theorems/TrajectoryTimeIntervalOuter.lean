import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable

/-!
# A trajectory stays in the step enclosure, inputs and all

The closed form splits a run into what the initial set carries and what the
inputs contributed, and the two are enclosed separately: `timeIntervalStep` for
the first, and a set the caller supplies for the second.

The input enclosure is a hypothesis, and unlike the sampled version it stays
one. `inputSolution_outer` encloses the contribution at the *end* of a step,
which is all `discretize` needs, since every step ends. Here `t` ranges over the
whole step, and one set has to cover every `t` at once.

That is Althoff's Prop. 3.3, and it needs `0 ∈ U`: only then is the enclosure at
`t` inside the one at `r`, each term scaling by `t^(i+1)` against `r^(i+1)`.
Proving it is not a matter of composing what is here — `plus` and `mtimes` carry
enclosure guarantees, not monotonicity, so a smaller enclosure cannot be lifted
into a larger one at the level of representations. It would take the Thm. 3.1
proof rerun over `[0,t]` with the target sets left at `r`.

Integrability is not a hypothesis: `InputIntegrable` derives it from `U` being
bounded, which every representation of a set of points is.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]
variable [Mtimes IntervalMat S]

set_option maxHeartbeats 1000000 in
theorem LinearSys.Trajectory.timeInterval_outer {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) ∈ construct Ud) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀) Ud) := by
  have hvoc := traj.variation_of_constants (le_refl (0:ℝ)) ht0
    (traj.intervalIntegrable_input (le_refl (0:ℝ)) ht0 hU)
  rw [sub_zero] at hvoc
  rw [hvoc]
  refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStep_outer hr hε R₀ ht0 htr
    (Set.mem_image_of_mem _ traj.init)

end CORALean.Real
