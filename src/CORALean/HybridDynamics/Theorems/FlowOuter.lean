module

public import CORALean.HybridDynamics.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryTimeIntervalOuter
public import CORALean.HybridDynamics.Operations.TimeIntervalStep
public import CORALean.HybridDynamics.Theorems.LinearEmbedding

@[expose] public section

/-!
# A stay is enclosed by the linear time-interval step

What `Location` holding `LinearSys` dynamics buys: the enclosure of a whole stay is `LinearSys`'s
over one step, applied on the location's own clock; `hT` is `subset_rfl` here. The invariant does
not appear: it can only shrink the enclosure, by intersecting with `ℓ.inv`, which
`TimeIntervalInvOuter` restates. `0 < τ` rather than `0 ≤ τ`, since `timeIntervalStep` divides by
the step length. Stated through `Location.timeIntervalStep` rather than the dynamics' own, since
`ℓ.dynamics` drops `S`.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory of the stay
* `u` – input trajectory
* `w` – disturbance trajectory
* `R₀` – initial set
* `Ud` – input contribution set
* `m` – Taylor order offset
* `t` – time within the stay

## Hypotheses
* `traj` – the curves are a stay of the location
* `h₀` – initial state lies in the initial set
* `hτ` – stay duration positive
* `hε` – step small enough for the Taylor order
* `ht0` – time nonnegative
* `htτ` – time within the stay duration
* `hU` – input set bounded
* `hUd` – input contribution holds the particular integral

## Conclusion
* state at the time lies in the time-interval step plus the input contribution
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
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
theorem Location.IsTrajectory.timeInterval_outer [∀ n, OfPoint (S n) (Vec ℝ n)]
    {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.IsTrajectory τ x u w) {R₀ Ud : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) (hU : Bornology.IsBounded (construct ℓ.inputSet))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat ℓ.dynamics.A) *ᵥ
      (toRealMat ℓ.dynamics.B *ᵥ u s + toRealVec ℓ.dynamics.c + toRealMat ℓ.dynamics.E *ᵥ w s))
      ∈ construct Ud) : -- --- CONCL ---
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀) Ud) :=
  (traj.linearSys h₀ traj.inputSet_mem).timeInterval_outer hτ
    subset_rfl hε ht0 htτ hU hUd

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
