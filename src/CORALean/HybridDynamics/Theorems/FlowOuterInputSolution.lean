import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
import CORALean.HybridDynamics.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Theorems.LinearEmbedding

/-!
# A stay is enclosed with the input contribution computed, not assumed

`FlowOuter.timeInterval_outer` leaves the input's contribution as a hypothesis
`hUd`, naming a set `Ud` the caller must already know contains this
trajectory's particular integral. `TimeIntervalOuterInputSolution` discharges
that hypothesis from properties of `ℓ.U` alone — convex, closed, bounded, and
containing the origin — so this restates the enclosure with no set named
after `u` at all: `inputSolution` supplies it, and it is the same for every
admissible input.

That is what makes `Invariant.flow`'s universal quantifier over trajectories
tractable: nothing here depends on which `u` a particular stay picked.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through lies in the location's time-interval
enclosure with the input contribution computed from `ℓ.U`, not named. -/
theorem Location.Trajectory.timeInterval_outer_inputSolution {ℓ : Location S L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) {R₀ : S n}
    (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct ℓ.U)) (hclosed : IsClosed (construct ℓ.U))
    (hbdd : Bornology.IsBounded (construct ℓ.U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.U)))
    (h0 : (0 : Vec ℝ n) ∈ construct ℓ.U) {t : ℝ} (ht0 : 0 ≤ t) (htτ : t ≤ τ) :
    x t ∈ construct (Plus.plus (ℓ.timeIntervalStep τ (m + 2) R₀)
      (ℓ.dynamics.inputSolution τ (m + 2) ℓ.U)) :=
  (traj.linearSys h₀).timeInterval_outer_inputSolution hτ subset_rfl hε ht0 htτ hconv hclosed hbdd
    hRconv hRclosed hRbdd h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
