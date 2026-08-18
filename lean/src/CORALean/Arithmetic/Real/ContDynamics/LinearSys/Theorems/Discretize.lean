import CORALean.Arithmetic.Real.ContDynamics.LinearSys.Operations
import CORALean.Arithmetic.Real.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# A sampled trajectory is a trajectory of the sampled system

Reading a continuous run at `0, Δt, 2Δt, ...` gives a run of `discretize`, so
every guarantee `LinearSysDT` already carries applies at the sample times and
none of it is proved twice.

Each step is variation of constants over `[kΔt, (k+1)Δt]`, where the propagator
is `e^{AΔt}` whatever `k` is.

The input set is a hypothesis: `stepInput` is an integral, and enclosing it is
where convexity of the input set is needed, which `ContSet` does not offer.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n]

set_option maxHeartbeats 10000 in
theorem LinearSys.Trajectory.discretize {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory R₀ U x u) (hΔt : 0 ≤ Δt)
    (hu : ∀ k : ℕ, IntervalIntegrable
      (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume (k * Δt) ((k + 1) * Δt))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).Trajectory R₀ Ud (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := by
    -- `toRealMat` is the identity at ℝ, but nothing states that as a rewrite
    have hreal : ∀ M : Mat ℝ n n, toRealMat M = M := fun _ => rfl
    have ha : (0 : ℝ) ≤ (k : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg k) hΔt
    have hab : (k : ℝ) * Δt ≤ ((k : ℝ) + 1) * Δt := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h := traj.variation_of_constants ha hab (hu k)
    have hstep : ((k : ℝ) + 1) * Δt - (k : ℝ) * Δt = Δt := by ring
    rw [hstep] at h
    simpa [LinearSys.discretize, LinearSys.stepInput, hreal] using h

end CORALean.Arithmetic.Real
