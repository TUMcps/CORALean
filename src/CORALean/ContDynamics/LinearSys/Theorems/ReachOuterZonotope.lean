import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContSet.Zonotope.Real.API

/-!
# Reachability at a zonotope, with nothing left to assume

One of two files where a `ContDynamics` statement names a representation, the
other being `TimeIntervalOuterZonotope`. The algorithms do not, and cannot: they
are written against `OuterContSet` alone. This says what happens when a
representation that *does* have the properties `inputSolution_outer` needs is
substituted in.

`Zonotope` has all of them, and the same three lemmas discharge all six
hypotheses: `mtimes` at an interval matrix returns a zonotope, so the remainder
product is convex, closed and bounded for exactly the reason `U` is.

The direction matters — `ContDynamics` may name `ContSet`, never the reverse —
so this lives here rather than beside the zonotope lemmas it uses.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

/-- The zonotope family, named locally because a generic theorem quantifies over
`S : ℕ → Type` and the elaborator cannot read that family off one member. -/
local notation "𝒵" => fun n => Zonotope (Vec ℝ n)

/-- The interval-matrix family, named for the same reason. -/
local notation "ℐ" => fun m n => Interval (Mat ℝ m n)

set_option maxHeartbeats 1000000 in
/-- Every trajectory of a linear system whose initial and input sets are
zonotopes stays in `reach`, at every sample time. The step, the Taylor order and
the bound `hε` relating them are all that is left to supply. -/
theorem LinearSys.Trajectory.reach_outer_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory (S := 𝒵) R₀ U x u) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (o k : ℕ) :
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach (S := 𝒵) o R₀
        (sys.inputSolution (S := 𝒵) Δt η U) k) :=
  traj.reach_outer_inputSolution hΔt η hε
    U.convex_construct U.isClosed_construct U.isBounded_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).convex_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).isClosed_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).isBounded_construct
    o k

end CORALean.Real
