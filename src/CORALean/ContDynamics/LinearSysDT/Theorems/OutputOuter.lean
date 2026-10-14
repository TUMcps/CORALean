module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

@[expose] public section

/-!
# The output of a discrete run lies in the output set of its reachable set

The two enclosures a run already carries, joined: `reach_outer` places the state
at step `k` in the reachable set, and `Trajectory.input` places the input at
that step in `U`, which is exactly the pair `outputSet_outer` asks for.

`U` appears twice in the conclusion, as the set the step was taken with and as
the set the output is read at. That is the same set by definition here — a
`LinearSysDT.CanonicalTrajectory` draws every step's input from one `U` — and it is why
an output equation stored on the system would be wrong for a *sampled* system,
where the two sets come apart.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
    [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.output_outer (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) {o : ℕ}
    (ho : 0 < o) (R₀ U : S n) {x u : ℕ → Vec ℝ n} (traj : sys.CanonicalTrajectory R₀ U x u) (k : ℕ)
        :
    out.eval (x k) (u k) ∈ construct (out.outputSet (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U) :=
  out.outputSet_outer _ _ (sys.reach_outer ho R₀ U traj k) (traj.input k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
