import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

/-!
# `reach` contains every trajectory at the sample times

The whole proof is `Discretize` handed to `LinearSysDT.reach_outer`: once a
sampled run is a discrete run, the discrete guarantee is the continuous one at
`0, Δt, 2Δt, ...`. Between the sample times it says nothing — that is
`TimeIntervalOuter`.

`Mtimes (Mat ℝ) S`, not `Mat 𝕋`: the propagated matrix is `e^{AΔt}`, which is
real whatever the system stores.

`reach_outer_inputSolution` is the same statement with the input enclosure named
rather than assumed.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Plus LinComb Reduce

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- Sampling and then running the discrete-time recursion; nothing here
combines, which is why `LinComb` is not asked for. -/
theorem LinearSys.Trajectory.reach_outer {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory R₀ U x u) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach o R₀ Ud k) :=
  LinearSysDT.reach_outer _ o R₀ Ud (traj.discretize hΔt hU hUd) k

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- The same, with the input set named rather than assumed: `inputSolution Δt η U`
encloses every step's contribution, so nothing about the input is left to the
caller beyond the properties of `U` itself. -/
theorem LinearSys.Trajectory.reach_outer_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) (o k : ℕ) :
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach o R₀ (sys.inputSolution Δt η U) k) :=
  LinearSysDT.reach_outer _ o R₀ _
    (traj.discretize_inputSolution hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd) k

end CORALean.Real
