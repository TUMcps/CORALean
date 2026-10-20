module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeInputSolution
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` contains every trajectory, inputs and all

The same as `reach_outer`, with the input set named rather than assumed:
`inputSolution Δt η U` encloses every step's contribution, so nothing about the
input is left to the caller beyond the properties of `U` itself.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `Δt` – sampling step
* `η` – Taylor order
* `o` – zonotope order
* `k` – step index

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hΔt` – step length positive
* `hT` – time domain contains the nonnegative reals
* `hε` – scaled norm small enough for the Taylor order
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image convex
* `hRclosed` – remainder image closed
* `hRbdd` – remainder image bounded
* `ho` – zonotope order positive

## Conclusion
* the trajectory's sample lies in the sampled reach set
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.IsCanonicalTrajectory.reach_outer_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) {o : ℕ} (ho : 0 < o)
    (k : ℕ) :
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach ⟨R₀, sys.inputSolution Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  LinearSysDT.reach_outer _ ho R₀ _
    (traj.discretize_inputSolution hΔt hT η hε hconv hclosed hbdd hRconv hRclosed hRbdd) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
