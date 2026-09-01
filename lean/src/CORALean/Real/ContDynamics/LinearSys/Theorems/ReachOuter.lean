import CORALean.Real.ContDynamics.LinearSys.Theorems.Discretize

/-!
# `reach` contains every trajectory at the sample times

The whole proof is `Discretize` handed to `LinearSysDT.reach_outer`: once a
sampled run is a discrete run, the discrete guarantee is the continuous one at
`0, Δt, 2Δt, ...` and there is nothing left to show.

Between the sample times it says nothing. Covering those needs a set enclosing
the curve over a step, which no operation offers yet.

`OuterContSet S ℝ`, not `S 𝕋`: the propagated matrix is `e^{AΔt}`, which is real.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory OuterContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]

set_option maxHeartbeats 10000 in
theorem LinearSys.Trajectory.reach_outer {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory R₀ U x u) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach o R₀ Ud k) :=
  LinearSysDT.reach_outer _ o R₀ Ud (traj.discretize hΔt hU hUd) k

end CORALean.Real
