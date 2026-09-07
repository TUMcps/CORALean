import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.HybridDynamics.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Theorems.LinearEmbedding

/-!
# A stay is enclosed by the linear time-interval step

What `Location` holding `LinearSys` dynamics buys: the enclosure of a whole stay
is `LinearSys`'s over one step, applied on the location's own clock. `hT` is
`subset_rfl` here — the stay is defined on `Set.Icc 0 τ` and on nothing else,
which is the case the time domain was made a parameter for.

The invariant does not appear here. It cannot make the enclosure unsound and can
only shrink it, and shrinking it means intersecting with `ℓ.inv` — left to
`TimeIntervalInvOuter`, which restates this theorem cut to the invariant at a
representation with an `And` instance.

`0 < τ` rather than `0 ≤ τ`: `timeIntervalStep` divides by the step length, and a
zero-length stay needs no enclosure of its own.

Stated through `Location.timeIntervalStep` rather than the dynamics' own:
`ℓ.dynamics` drops `S`, and a use site would have to name the family back in a
statement its `ℓ` already pinned.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through lies in the location's time-interval
enclosure, the initial set and the input contribution named by the caller. -/
theorem Location.Trajectory.timeInterval_outer {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) {R₀ Ud : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ u s)
      ∈ construct Ud) :
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀) Ud) :=
  (traj.linearSys h₀).timeInterval_outer hτ subset_rfl hε ht0 htτ hU hUd

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
