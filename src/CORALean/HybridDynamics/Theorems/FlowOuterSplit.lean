module

public import CORALean.HybridDynamics.Theorems.Basic
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSplit
public import CORALean.HybridDynamics.Operations.TimeIntervalStepSplit
public import CORALean.HybridDynamics.Theorems.LinearEmbedding

@[expose] public section

/-!
# A stay is enclosed with no assumption on where the input set sits

`FlowOuterInputSolution` computes the input contribution but pays for it with
`0 ∈ ℓ.inputSet`, which a location's combined input set need not satisfy — a constant drift
such as gravity, the offset `c`, is exactly an input set that misses the origin.
`TimeIntervalOuterSplit` drops that hypothesis, and this is it at a location.

Every remaining side condition comes off `ConvexSet` and `CompactSet` rather
than off the caller, so the enclosure holds of every stay of every location at
a representation carrying those two instances — nothing about `u`, and nothing
about `ℓ.U` or `ℓ.W`, survives into the statement.
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

/-- Every state a stay passes through lies in the location's split
time-interval enclosure, wherever the location's input set sits. -/
theorem Location.IsTrajectory.timeInterval_outer_split [∀ n, OfPoint (S n) (Vec ℝ n)]
    [∀ n, Recenter (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
    [∀ n, CompactSet (S n) (Vec ℝ n)]
    {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.IsTrajectory τ x u w)
    {R₀ : S n} (h₀ : x 0 ∈ construct R₀) (hτ : 0 < τ) {m : ℕ}
    (hε : ‖τ • toRealMat ℓ.dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t ≤ τ) :
    x t ∈ construct (ℓ.timeIntervalStepSplit τ (m + 2) R₀) :=
  (traj.linearSys h₀ traj.inputSet_mem).timeInterval_outer_split hτ subset_rfl hε ht0 htτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
