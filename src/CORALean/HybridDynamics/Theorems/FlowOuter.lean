import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.HybridDynamics.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Theorems.LinearEmbedding

/-!
# A stay is enclosed by the linear time-interval step

What `Location` holding `LinearSys` dynamics buys: the enclosure of a whole stay
is `LinearSys`'s over one step, applied on the location's own clock. `hT` is
`subset_rfl` here — the stay is defined on `Set.Icc 0 τ` and on nothing else,
which is the case the time domain was made a parameter for.

The invariant does not appear. It cannot make the enclosure unsound and can only
shrink it, and shrinking it means intersecting with `ℓ.inv` — the same
intersection the guard wants and the same missing interface, so it is left to a
caller with a representation that can do it, exactly as in `JumpOuter`.

`0 < τ` rather than `0 ≤ τ`: `timeIntervalStep` divides by the step length. A
zero-length stay needs no enclosure of its own, the state being the one it
entered with.

Stated through `Location.timeIntervalStep` rather than through the dynamics'
own: `ℓ.dynamics` drops `S`, and a use site would have to name the family back
in a statement its `ℓ` already pinned.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]

/-- Every state a stay passes through lies in the location's time-interval
enclosure, the initial set and the input contribution named by the caller. -/
theorem Location.Trajectory.timeInterval_outer {ℓ : Location S L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) {R₀ Ud : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ u s)
      ∈ construct Ud) :
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀) Ud) :=
  (traj.linearSys h₀).timeInterval_outer hτ subset_rfl hε ht0 htτ hU hUd

end CORALean.Real
