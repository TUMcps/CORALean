module

public import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the output set holds along every run

`holds_of_reach` at the output rather than the state, and the reason to have
both: a requirement on `y` is not a requirement on `x` pulled back, `C` being
in general not invertible.

Per step, as `holds_of_reach` is, and for the same reason: `reach` returns one
set per step.
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
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ r)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.holds_of_output (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) {o : ℕ}
    (ho : 0 < o) (R₀ U : S n) (spec : Specification ContSet) {x u : ℕ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (out.outputSet (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U)))
    : -- --- STMT ---
    spec.Holds {out.eval (x k) (u k)} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer out ho R₀ U traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
