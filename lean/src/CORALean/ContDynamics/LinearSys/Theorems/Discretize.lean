import CORALean.ContDynamics.LinearSys.Operations
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter

/-!
# A sampled trajectory is a trajectory of the sampled system

Reading a continuous run at `0, Δt, 2Δt, ...` gives a run of `discretize`, so
every guarantee `LinearSysDT` already carries applies at the sample times and
none of it is proved twice.

Each step is variation of constants over `[kΔt, (k+1)Δt]`, where the propagator
is `e^{AΔt}` whatever `k` is.

The input set is a hypothesis, because enclosing an integral needs convexity and
closedness of `U`, which `ContSet` does not offer. Boundedness of `U` is asked
for instead of integrability of `u`, which `InputIntegrable` derives from it.

`discretize_inputSolution` discharges that hypothesis where the representation
does offer them, naming `inputSolution Δt η U` — one set for every step, since
every step is `Δt` long. The general form stays for representations that are
not convex.
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
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
set_option maxHeartbeats 10000 in
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

set_option maxHeartbeats 40000 in
/-- The same, with the input set named rather than assumed. Available to a
representation that is convex and closed; `Zonotope` is both. -/
theorem LinearSys.Trajectory.discretize_inputSolution [Mtimes (fun m n => Interval (Mat ℝ m n)) S]
    {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat ℝ m n))
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat ℝ m n))
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat ℝ m n))
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) :
    (sys.discretize Δt).Trajectory R₀ (sys.inputSolution Δt η U)
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) :=
  traj.discretize hΔt.le hbdd
    (traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd)

end CORALean.Real
