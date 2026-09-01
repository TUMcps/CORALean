import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContSet.ConZonotope.API

/-!
# Reachability at a constrained zonotope, with nothing left to assume

`reach_outer_inputSolution` with the representation substituted in, exactly as
for a zonotope. The three lemmas that discharge all six hypotheses are the
constrained zonotope's own — compactness comes from `domain` being a polytope,
not from the coefficient cube.

Here rather than beside the constrained-zonotope lemmas it uses, since
`ContDynamics` may name `ContSet` and never the reverse.
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

set_option maxHeartbeats 1000000 in
/-- Every trajectory of a linear system whose initial and input sets are
constrained zonotopes stays in `reach`, at every sample time. -/
theorem LinearSys.Trajectory.reach_outer_conZonotope {sys : LinearSys 𝕋 n}
    {R₀ U : ConZonotope (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory (S := 𝒞) R₀ U x u) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (o k : ℕ) :
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach (S := 𝒞) o R₀
        (sys.inputSolution (S := 𝒞) Δt η U) k) :=
  traj.reach_outer_inputSolution hΔt η hε
    U.convex_construct U.isClosed_construct U.isBounded_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒞) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).convex_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒞) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).isClosed_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒞) (MatExp.inputRemainder (toRealMat sys.A) Δt η)
      U).isBounded_construct
    o k

end CORALean.Real
