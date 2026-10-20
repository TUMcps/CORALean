module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeMatZonotope
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `discretizeMatZonotope`'s trajectory lands in `reach`

`DiscretizeEnclosureReach` again, and the point of it: the whole proof is `discretizeMatZonotope`
handed to the same `LinParamSysDT.reach_outer`, which is not re-run at a matrix zonotope but simply
run: `reach` quantifies over the matrix family, so the recursion never mentioned interval matrices.
`Mtimes 𝕄𝒵 S`, not `Mtimes ℐ S`: what multiplies a reachable set is now a matrix zonotope, so the
correlations between the entries of `e^{AΔt}` survive the step instead of being dropped at the box.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `Ud` – sampled input set
* `x` – state trajectory
* `u` – input signal
* `Δt` – sampling step
* `η` – Taylor order
* `o` – zonotope order
* `k` – step index

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hΔt` – step length nonnegative
* `hT` – time domain contains the nonnegative reals
* `hU` – input set bounded
* `hUd` – step inputs lie in the sampled input set
* `hε` – scaled norm small enough for the Taylor order
* `ho` – zonotope order positive

## Conclusion
* the sample after the given steps lies in the matrix-zonotope reach set
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄𝒵 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sampling into the matrix-zonotope system and then running its recursion. -/
theorem LinearSys.IsCanonicalTrajectory.discretizeMatZonotope_mem_reach {sys : LinearSys 𝕋 n}
    {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {η : ℕ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o)
    (k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretizeMatZonotope Δt η).reach ⟨R₀, Ud, 0, k⟩ ⟨o, ho⟩) :=
  (sys.discretizeMatZonotope Δt η).reach_outer ho R₀ Ud
    (traj.discretizeMatZonotope hΔt hT hU hUd hε) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
