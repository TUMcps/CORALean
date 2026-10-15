module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.OutputOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the output set holds along every run

`LinearSysDT.holds_of_output`'s statement, at a system matrix ranging over a
set: `holds_of_reach` at the output rather than the state, for the same
reason `LinearSysDT`'s pair exists — `C` is in general not invertible.
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
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ r)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.holds_of_output (sys : LinParamSysDT 𝕄 n) (out : OutputEq 𝕋 n n r) {o : ℕ}
    (ho : 0 < o) (R₀ U : S n) (spec : Specification ContSet) {x u : ℕ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (out.outputSet (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U))) :
    spec.Holds {out.eval (x k) (u k)} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer out ho R₀ U traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
