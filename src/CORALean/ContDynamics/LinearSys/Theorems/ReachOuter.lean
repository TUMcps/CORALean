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
statements below ask only for `[0, KΔt]` and pay for it by unrolling the
discrete recursion themselves — `LinearSysDT.Trajectory` is total in the step
count, so there is nothing bounded to hand it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
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
theorem aux_step_subset_horizon {T : Set ℝ} {Δt : ℝ} {K k : ℕ} (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hk : k < K) :
    Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T := by
  refine fun s hs => hT ⟨le_trans (mul_nonneg (Nat.cast_nonneg k) hΔt) hs.1, ?_⟩
  refine le_trans hs.2 (mul_le_mul_of_nonneg_right ?_ hΔt)
  exact_mod_cast Nat.succ_le_of_lt hk

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- The same conclusion over a bounded horizon: `K` steps see the flow on
`[0, KΔt]` and nothing beyond it, which is what a one-step method and a hybrid
location can actually supply.

The discrete recursion is unrolled here rather than handed to
`LinearSysDT.reach_outer`: that asks for a `LinearSysDT.Trajectory`, which is
total in the step count, and a bounded domain has no such run to give it. -/
theorem LinearSys.Trajectory.reach_outer_horizon {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) (o : ℕ) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct ((sys.discretize Δt).reach o R₀ Ud k) := by
  intro k
  induction k with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * Δt) ∈ construct R₀
    simpa using traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    show x (((k + 1 : ℕ) : ℝ) * Δt) ∈ construct (reduce (plus
      (Mtimes.mtimes (sys.discretize Δt).A ((sys.discretize Δt).reach o R₀ Ud k)) Ud) o)
    rw [hcast, traj.discretize_step hΔt hU k (aux_step_subset_horizon hΔt hT hkK)]
    exact reduce_outer _ _ (plus_outer _ _
      (Set.add_mem_add
        (Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (ih hkK.le))))
        (hUd k hkK)))

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
      (aux_step_subset_horizon hΔt.le hT hk)) o

end CORALean.Real
