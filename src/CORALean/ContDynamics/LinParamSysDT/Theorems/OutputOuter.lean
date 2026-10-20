module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

@[expose] public section

/-!
# The output of a discrete run lies in the output set of its reachable set

`LinearSysDT.output_outer`'s statement, at a system matrix ranging over a set:
`reach_outer` places the state at step `k` in the reachable set and
`IsCanonicalTrajectory.input` places the input at that step in `U`, exactly the pair
`outputSet_outer` asks for.

`out : OutputEq 𝕋 n n r` carries its own scalar `𝕋`, separate from the
system's matrix-set family `𝕄`: an uncertain system matrix paired with an
exactly-known output map is the normal case here, not an oversight.

## Inputs
* `sys` – system
* `out` – output equation
* `o` – maximum zonotope order
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `k` – step

## Hypotheses
* `ho` – order positive
* `traj` – discrete-time trajectory

## Conclusion
* the run's output lies in the output set of the reachable set
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes 𝕄 S] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.output_outer (sys : LinParamSysDT 𝕄 n) (out : OutputEq 𝕋 n n r) {o : ℕ}
    (ho : 0 < o) (R₀ U : S n) {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u)
    (k : ℕ) :
    out.eval (x k) (u k) ∈ construct (out.outputSet (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U) :=
  out.outputSet_outer _ _ (sys.reach_outer ho R₀ U traj k) (traj.input k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
