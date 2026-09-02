import CORALean.ContDynamics.LinearSys.Operations
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
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
theorem LinearSys.Trajectory.discretize {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory R₀ U x u) (hΔt : 0 ≤ Δt)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).Trajectory R₀ Ud (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := by
    have ha : (0 : ℝ) ≤ (k : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg k) hΔt
    have hab : (k : ℝ) * Δt ≤ ((k : ℝ) + 1) * Δt := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h := traj.variation_of_constants ha hab (traj.intervalIntegrable_input ha hab hU)
    have hstep : ((k : ℝ) + 1) * Δt - (k : ℝ) * Δt = Δt := by ring
    rw [hstep] at h
    simpa [LinearSys.discretize, LinearSys.stepInput] using h

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- The same, with the input set named rather than assumed. Available to a
representation that is convex and closed; `Zonotope` is both. -/
theorem LinearSys.Trajectory.discretize_inputSolution [Mtimes ℐ S]
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
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) :
    (sys.discretize Δt).Trajectory R₀ (sys.inputSolution Δt η U)
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) :=
  traj.discretize hΔt.le hbdd
    (traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd)

end CORALean.Real
