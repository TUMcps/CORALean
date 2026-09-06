import CORALean.ContDynamics.LinParamSysDT.Theorems.OutputOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the output set holds along every run

`LinearSysDT.holds_of_output`'s statement, at a system matrix ranging over a
set: `holds_of_reach` at the output rather than the state, for the same
reason `LinearSysDT`'s pair exists — `C` is in general not invertible.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n r : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes 𝕄 S] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.holds_of_output (sys : LinParamSysDT 𝕄 n) (out : OutputEq 𝕋 n n r) (o : ℕ)
    (R₀ U : S n) (spec : Specification (Vec ℝ r)) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (out.outputSet (sys.reach o R₀ U k) U))) :
    spec.Holds {out.eval (x k) (u k)} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer out o R₀ U traj k)) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
