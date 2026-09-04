import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter

/-!
# A sampled trajectory is a trajectory of the sampled system

Reading a continuous run at `0, Δt, 2Δt, ...` gives a run of `discretize`, so
every guarantee `LinearSysDT` already carries applies at the sample times. Each
step is variation of constants over `[kΔt, (k+1)Δt]`, where the propagator is
`e^{AΔt}` whatever `k` is.

The set enclosing the input is a hypothesis, since enclosing an integral needs
`U` convex and closed and `ContSet` does not offer that.
`discretize_inputSolution` discharges it where the representation does, naming
`inputSolution Δt η U` — one set for every step, all steps being `Δt` long.

`discretize_step` is one such step and asks for the flow on that step only;
`discretize` is every step at once and so asks for all of forward time. That
split is what the bounded-horizon reachability statements are built on.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

/-- Every step of a nonnegative length sits in forward time, so a domain
covering `[0, ∞)` covers each of them. -/
theorem aux_step_subset {T : Set ℝ} {Δt : ℝ} (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T) (k : ℕ) :
    Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T :=
  fun _ hs => hT (le_trans (mul_nonneg (Nat.cast_nonneg k) hΔt) hs.1)

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- One step of the sampled recursion, from the flow on that step alone. Every
bounded-horizon statement is this iterated, so it is stated apart from
`discretize`, which needs every step at once. -/
theorem LinearSys.Trajectory.discretize_step {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hΔt : 0 ≤ Δt) (hU : Bornology.IsBounded (construct U)) (k : ℕ)
    (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) :
    x (((k : ℝ) + 1) * Δt)
      = toRealMat (sys.discretize Δt).A *ᵥ x ((k : ℝ) * Δt) + sys.stepInput u Δt k := by
  have hab : (k : ℝ) * Δt ≤ ((k : ℝ) + 1) * Δt := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h := traj.variation_of_constants hT hab (traj.intervalIntegrable_input hT hab hU)
  have hstep : ((k : ℝ) + 1) * Δt - (k : ℝ) * Δt = Δt := by ring
  rw [hstep] at h
  simpa [LinearSys.discretize, LinearSys.stepInput] using h

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- Every step at once, so the domain has to be all of forward time: the discrete
trajectory produced is indexed by all of `ℕ`, and `LinearSysDT.Trajectory` has no
partial form. A bounded domain goes through `reach_outer_horizon` instead. -/
theorem LinearSys.Trajectory.discretize {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Ici 0 ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).Trajectory R₀ Ud (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := by
    simpa using traj.discretize_step hΔt hU k (aux_step_subset hΔt hT k)

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- The same, with the input set named rather than assumed. Available to a
representation that is convex and closed; `Zonotope` is both. -/
theorem LinearSys.Trajectory.discretize_inputSolution [Mtimes ℐ S]
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
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) :
    (sys.discretize Δt).Trajectory R₀ (sys.inputSolution Δt η U)
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) :=
  traj.discretize hΔt.le hT hbdd
    (fun k => traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd k
      (aux_step_subset hΔt.le hT k))

end CORALean.Real
