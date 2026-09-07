import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotope
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

/-!
# `discretizeMatZonotope`'s trajectory lands in `reach`

`DiscretizeEnclosureReach` again, and the point of it: the whole proof is
`discretizeMatZonotope` handed to the same `LinParamSysDT.reach_outer`, which
is not re-run at a matrix zonotope but simply run — `reach` quantifies over the
matrix family, so the recursion never mentioned interval matrices to begin
with.

`Mtimes 𝕄𝒵 S`, not `Mtimes ℐ S`: what multiplies a reachable set is now a
matrix zonotope, so the correlations between the entries of `e^{AΔt}` survive
the step instead of being dropped at the box.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄𝒵 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sampling into the matrix-zonotope system and then running its recursion. -/
theorem LinearSys.Trajectory.discretizeMatZonotope_mem_reach {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretizeMatZonotope Δt η).reach o ho R₀ Ud k) :=
  (sys.discretizeMatZonotope Δt η).reach_outer ho R₀ Ud
    (traj.discretizeMatZonotope hΔt hT hU hUd hε) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
