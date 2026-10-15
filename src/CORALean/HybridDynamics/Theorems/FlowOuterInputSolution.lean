module

public import CORALean.HybridDynamics.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.IsClassicalTrajectoryIsTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
public import CORALean.HybridDynamics.Operations.TimeIntervalStep
public import CORALean.HybridDynamics.Theorems.LinearEmbedding

@[expose] public section

/-!
# A stay is enclosed with the input contribution computed, not assumed

`FlowOuter.timeInterval_outer` leaves the input's contribution as a hypothesis
`hUd`, naming a set `Ud` the caller must already know contains this
trajectory's particular integral. `TimeIntervalOuterInputSolution` discharges
that hypothesis from properties of `ℓ.inputSet` alone — convex, closed, bounded, and
containing the origin — so this restates the enclosure with no set named
after `u` at all: `inputSolution` supplies it, and it is the same for every
admissible input.

That is what makes `Invariant.flow`'s universal quantifier over trajectories
tractable: nothing here depends on which `u` a particular stay picked.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through lies in the location's time-interval
enclosure with the input contribution computed from `ℓ.inputSet`, not named. -/
theorem Location.IsTrajectory.timeInterval_outer_inputSolution
    [∀ n, OfPoint (S n) (Vec ℝ n)] {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.IsTrajectory τ x u w) {R₀ : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct ℓ.inputSet)) (hclosed : IsClosed (construct ℓ.inputSet))
    (hbdd : Bornology.IsBounded (construct ℓ.inputSet))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.inputSet)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.inputSet)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.inputSet)))
    (h0 : (0 : Vec ℝ n) ∈ construct ℓ.inputSet) {t : ℝ} (ht0 : 0 ≤ t) (htτ : t ≤ τ) :
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀)
      (ℓ.dynamics.inputSolution τ (m + 2) ℓ.inputSet)) :=
  ((traj.linearSys h₀ traj.inputSet_mem).trajectory (convex_Icc 0 τ) ⟨le_rfl, hτ.le⟩
    hbdd).timeInterval_outer_inputSolution hτ subset_rfl hε ht0 htτ hconv hclosed hbdd
    hRconv hRclosed hRbdd h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
