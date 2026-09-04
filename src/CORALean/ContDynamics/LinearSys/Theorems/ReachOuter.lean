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

Both ask for all of forward time, which is what `discretize` needs. The horizon
statements below ask only for `[0, KΔt]`: `discretize_horizon` samples that
into a `LinearSysDT.TrajectoryOn K`, and `reach_outer_horizon` is
`LinearSysDT.reach_outer_on` handed that — no recursion of its own.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
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
theorem LinearSys.Trajectory.reach_outer {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) (o k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretize Δt).reach o R₀ Ud k) :=
  LinearSysDT.reach_outer _ o R₀ Ud (traj.discretize hΔt hT hU hUd) k

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- The same, with the input set named rather than assumed: `inputSolution Δt η U`
encloses every step's contribution, so nothing about the input is left to the
caller beyond the properties of `U` itself. -/
theorem LinearSys.Trajectory.reach_outer_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
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
    (traj.discretize_inputSolution hΔt hT η hε hconv hclosed hbdd hRconv hRclosed hRbdd) k

/-- Step `k` of a run of `K` steps lies inside the horizon. -/
theorem step_subset_horizon {T : Set ℝ} {Δt : ℝ} {K k : ℕ} (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hk : k < K) :
    Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T := by
  refine fun s hs => hT ⟨le_trans (mul_nonneg (Nat.cast_nonneg k) hΔt) hs.1, ?_⟩
  refine le_trans hs.2 (mul_le_mul_of_nonneg_right ?_ hΔt)
  exact_mod_cast Nat.succ_le_of_lt hk

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- The run sampled from `[0, KΔt]` alone: `discretize_step` iterated, at the
domain `step_subset_horizon` carves out. A `TrajectoryOn K`, not a total
`Trajectory` — nothing pins `x` or `u` past step `K`. -/
theorem LinearSys.Trajectory.discretize_horizon {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).TrajectoryOn R₀ Ud K
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k hk := hUd k hk
  step k hk := by simpa using traj.discretize_step hΔt hU k (step_subset_horizon hΔt hT hk)

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- The same conclusion over a bounded horizon: `K` steps see the flow on
`[0, KΔt]` and nothing beyond. `discretize_horizon` handed to `reach_outer_on`
— no recursion of its own. -/
theorem LinearSys.Trajectory.reach_outer_horizon {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct ((sys.discretize Δt).reach o R₀ Ud k) :=
  (sys.discretize Δt).reach_outer_on o R₀ Ud (traj.discretize_horizon hΔt hT hU hUd)

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- The horizon statement with the input enclosure named rather than assumed.
Only the steps inside the horizon are enclosed, which is exactly what
`stepInput_outer` gives from a domain covering them. -/
theorem LinearSys.Trajectory.reach_outer_horizon_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct
      ((sys.discretize Δt).reach o R₀ (sys.inputSolution Δt η U) k) :=
  traj.reach_outer_horizon hΔt.le hT hbdd
    (fun k hk => traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd k
      (step_subset_horizon hΔt.le hT hk)) o

end CORALean.Real
