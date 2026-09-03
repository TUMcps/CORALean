import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

/-!
# The output of a discrete run lies in the output set of its reachable set

The two enclosures a run already carries, joined: `reach_outer` places the state
at step `k` in the reachable set, and `Trajectory.input` places the input at
that step in `U`, which is exactly the pair `outputSet_outer` asks for.

`U` appears twice in the conclusion, as the set the step was taken with and as
the set the output is read at. That is the same set by definition here — a
`LinearSysDT.Trajectory` draws every step's input from one `U` — and it is why
an output equation stored on the system would be wrong for a *sampled* system,
where the two sets come apart.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

theorem LinearSysDT.output_outer (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) (o : ℕ)
    (R₀ U : S n) {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    out.eval (x k) (u k) ∈ construct (out.outputSet (sys.reach o R₀ U k) U) :=
  out.outputSet_outer _ _ (sys.reach_outer o R₀ U traj k) (traj.input k)

end CORALean.Real
